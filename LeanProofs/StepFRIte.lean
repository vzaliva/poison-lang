/-
  StepFRIte.lean - Fault-robustness proof for the ite (conditional) case.

  Contains stepFR_ite_with_expr_proof (which dispatches on the typechecking
  mode: known-true guard, known-false guard, or standard conservative join),
  stepFRSingleRunFinalCleanPcTrue_ite_maskedReg_with_expr_proof, and the
  branch-join transport lemmas they use. The `matchGuard` structure lemmas are
  in `MatchGuardLemmas`.
-/
import LeanProofs.StepFR
import LeanProofs.MatchGuardLemmas
import LeanProofs.FootprintTyping
import LeanProofs.JoinMemberTransport
import LeanProofs.VarEnvPreservation

open List
open List.Mem
open Std
open scoped MemoryTypeEnv

variable {registry : ExternRegistry}

/-- The frame of a run holds for every regime whose tags (with a descriptor) the
    run's final regime defines. -/
private theorem KeepsFootprints.mono_regime {tm : TagMeaning} {R R' : Regime}
    {θ : RealizationMap} {μ μ' : Memory} (h : KeepsFootprints tm R θ μ μ')
    (hR : ∀ k d, tm.lookup k = some d → R'.lookup? k ≠ none → R.lookup? k ≠ none) :
    KeepsFootprints tm R' θ μ μ' :=
  fun k d hd hk => h k d hd (hR k d hd hk)

/-- Stability between two points of one run, from the frames from its start:
    the prefix to `μ1` and the whole run to `μ2` keep the footprints of every
    tag of the final regime. -/
private theorem predSatStable_mid {predSat : PredSat} {tm : TagMeaning} {nl : Loc}
    {R1 R2 : Regime} {θ θ1 θ2 : RealizationMap} {μ μ1 μ2 : Memory}
    (hlaws : PredSatLaws predSat tm) (hbelow : FootprintBelow tm nl)
    (hM1 : MapKeepsBelow nl θ θ1) (hM2 : MapKeepsBelow nl θ θ2)
    (hF1 : KeepsFootprints tm R1 θ μ μ1) (hF2 : KeepsFootprints tm R2 θ μ μ2)
    (hR : ∀ k d, tm.lookup k = some d → R2.lookup? k ≠ none → R1.lookup? k ≠ none) :
    PredSatStable predSat tm R2 θ1 θ2 μ1 μ2 := by
  refine predSatStable_of_frame hlaws hbelow (fun l hl => (hM2 l hl).trans (hM1 l hl).symm) ?_
  intro k d hd hk l hl a ha
  have hlt : l < nl := hbelow k d hd l hl
  have ha0 : θ.lookup l = some a := by rw [← hM1 l hlt]; exact ha
  exact (hF1 k d hd (hR k d hd hk) l hl a ha0).symm.trans (hF2 k d hd hk l hl a ha0)

lemma qtypCleanUnder_transport_pure_regime_of_toPExpr
    (ctx : TypeContext) (e : Expr) (pe : PExpr) (fuel : Nat) (res : TypeResult)
    (hpe : Expr.toPExpr? e = some pe)
    (htc : typecheckExpr { ctx with pureCtx := true } e fuel = .ok res) :
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

lemma runtimeInstantiatesCtx_transport_mem_subset_tag_insert_true
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

theorem consistentWithRegimeMasked_transport_ctxAfter_pure_to_ctx_insert_true
    (masked : Tag → Prop) (predSat : PredSat) (ctx : TypeContext) (res : TypeResult)
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
      consistentWithRegimeMasked masked predSat
        (ctxAfter { ctx with pureCtx := true } res).regime
        (ctxAfter { ctx with pureCtx := true } res) μ ρ θ) :
    consistentWithRegimeMasked masked predSat
      ({ ctx with tagEnv := ctx.tagEnv.insert kTrue ⟨true, depsTrue⟩ }).regime
      ({ ctx with tagEnv := ctx.tagEnv.insert kTrue ⟨true, depsTrue⟩ }) μ ρ θ := by
  rcases hcwr with ⟨hlocs, hvars, hclos⟩
  refine ⟨?_, ?_, ?_⟩
  · intro l qt k hlookup hguard hRdef
    have hlookupRes : res.memEnv'.lookup l = some qt := hmem_bridge l qt k hlookup hguard hRdef
    cases hbctx : ctx.regime.lookup? k with
    | none =>
        exact Or.inr <| False.elim (hRdef hbctx)
    | some b =>
        have hbres : res.regime'.lookup? k = some b := hreg_bridge k b hbctx
        have hloc :=
          hlocs l qt k
            (by
              unfold ctxAfter
              exact hlookupRes)
            hguard
            (by
              unfold ctxAfter
              intro hnone
              rw [hbres] at hnone
              contradiction)
        rcases hloc with hmasked | hloc
        · exact Or.inl hmasked
        · cases hloc with
          | noPred_ok hpred =>
              exact Or.inr (locsRegime.noPred_ok (l, qt) hpred)
          | guardOnly_ok k' hgo =>
              exact Or.inr (locsRegime.guardOnly_ok (l, qt) k' hgo)
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
              exact Or.inr <|
                locsRegime.withPred_ok (l, qt) k' arg_name pred_body var_env a n b'
                  hclos hbctx' hreal hmem hconsist
  · intro x qt k hlookup hguard hRdef
    cases hbctx : ctx.regime.lookup? k with
    | none =>
        exact Or.inr <| False.elim (hRdef hbctx)
    | some b =>
        have hbres : res.regime'.lookup? k = some b := hreg_bridge k b hbctx
        have hvar :=
          hvars x qt k
            (by
              unfold ctxAfter
              exact hlookup)
            hguard
            (by
              unfold ctxAfter
              intro hnone
              rw [hbres] at hnone
              contradiction)
        rcases hvar with hmasked | hvar
        · exact Or.inl hmasked
        · cases hvar with
          | noPred_ok hpred =>
              exact Or.inr (varsRegime.noPred_ok (x, qt) hpred)
          | guardOnly_ok k' hgo =>
              exact Or.inr (varsRegime.guardOnly_ok (x, qt) k' hgo)
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
              exact Or.inr <|
                varsRegime.withPred_ok (x, qt) k' arg_name pred_body var_env v b'
                  hclos hbctx' hvarLookup hconsist
  · intro x qt v hlookup hlookup_v
    have hlookupRes :
        (ctxAfter { ctx with pureCtx := true } res).varEnv.lookup x = some qt := by
      unfold ctxAfter
      exact hlookup
    have hcapRes :
        closureCapturedVarsRegimeMasked masked predSat
          (ctxAfter { ctx with pureCtx := true } res).regime
          qt μ θ v :=
      hclos x qt v hlookupRes hlookup_v
    exact
      closureCapturedVarsRegimeMasked_transport_lookup_back
        (masked := masked) (predSat := predSat)
        (R := (ctxAfter { ctx with pureCtx := true } res).regime)
        (R' := ({ ctx with tagEnv := ctx.tagEnv.insert kTrue ⟨true, depsTrue⟩ }).regime)
        (μ := μ)
        (hlookup_back := by
          intro k b hk
          simpa [ctxAfter] using hreg_bridge k b hk)
        hcapRes

/-- Side-neutral skeleton for `consistentWithRegime_join_from_{left,right}`.
The two divergence points between the mirror lemmas are abstracted as
hypotheses: `hlookup_back` (the `joinRegimes` back-lookup) and `hguard_implies`
(the `joinMemEnvsStrong` `guardClosure` membership transport). `resSide` is the
operand we transport back from (`resLeft` for the left wrapper, `resRight` for
the right). -/
private lemma consistentWithRegime_join_from_side
  (predSat : PredSat) (ctx : TypeContext)
  (resLeft resRight res resSide : TypeResult)
  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (hmemEnv : res.memEnv' = joinMemEnvsStrong resLeft.memEnv' resRight.memEnv')
  (hlookup_back :
    ∀ k b, (ctxAfter ctx res).regime.lookup? k = some b →
      (ctxAfter ctx resSide).regime.lookup? k = some b)
  (hguard_implies :
    ∀ (l : Loc) (qt : QTyp) (k' : Tag) (arg_name : Name)
      (pred_body : PExpr) (var_env : CapturedVarEnv),
      (joinMemEnvsStrong resLeft.memEnv' resRight.memEnv').lookup l = some qt →
      qt.pred = Predicate.guardClosure k' arg_name pred_body var_env →
      ∃ qtSide, resSide.memEnv'.lookup l = some qtSide ∧
        qtSide.pred = Predicate.guardClosure k' arg_name pred_body var_env)
  (hcwr :
    consistentWithRegime predSat
      (ctxAfter ctx resSide).regime
      (ctxAfter ctx resSide) μ ρ θ) :
  consistentWithRegime predSat
    (ctxAfter ctx res).regime
    (ctxAfter ctx res) μ ρ θ := by
  unfold consistentWithRegime at hcwr ⊢
  refine ⟨?_, ?_, ?_⟩
  · intro l qt k hlookup hguard hRdef
    cases hpred : qt.pred with
    | noPred =>
        simp [qtypGuardTag, hpred] at hguard
    | guardOnly k' =>
        exact locsRegime.guardOnly_ok (l, qt) k' hpred
    | guardClosure k' arg_name pred_body var_env =>
        have hk_eq : k' = k := by
          have : some k' = some k := by
            calc
              some k' = qtypGuardTag qt := by simp [qtypGuardTag, hpred]
              _ = some k := hguard
          exact Option.some.inj this
        rcases
            hguard_implies l qt k' arg_name pred_body var_env
              (by simpa [ctxAfter, hmemEnv] using hlookup)
              hpred
          with ⟨qtSide, hlookupSide, hpredSide⟩
        have hRdef_side : (ctxAfter ctx resSide).regime.lookup? k' ≠ none := by
          intro hnone
          cases hkres : (ctxAfter ctx res).regime.lookup? k' with
          | none =>
              exact hRdef (by simpa [ctxAfter, hk_eq] using hkres)
          | some b =>
              have hk_side : (ctxAfter ctx resSide).regime.lookup? k' = some b :=
                hlookup_back k' b hkres
              rw [hk_side] at hnone
              contradiction
        have hguard_side : qtypGuardTag qtSide = some k' := by
          simp [qtypGuardTag, hpredSide]
        have hloc_side :=
          hcwr.1 l qtSide k'
            (by simpa [ctxAfter] using hlookupSide)
            hguard_side
            hRdef_side
        cases hloc_side with
        | noPred_ok hnp =>
            simp [qtypGuardTag, hpredSide] at hnp
        | guardOnly_ok _ hgo =>
            simp [hpredSide] at hgo
        | withPred_ok kSide arg_name' pred_body' var_env' a n b hclos hreg hreal hmem hcons =>
            have hpred_ctor_eq :
                Predicate.guardClosure kSide arg_name' pred_body' var_env' =
                  Predicate.guardClosure k' arg_name pred_body var_env := by
              calc
                Predicate.guardClosure kSide arg_name' pred_body' var_env' = qtSide.pred := by
                  simpa using hclos.symm
                _ = Predicate.guardClosure k' arg_name pred_body var_env := hpredSide
            cases hpred_ctor_eq
            have hpred_eq : qtSide.pred = qt.pred := by
              simp [hpredSide, hpred]
            have hreg_res : (ctxAfter ctx res).regime.lookup? k' = some b := by
              cases hkres : (ctxAfter ctx res).regime.lookup? k' with
              | none =>
                  exact False.elim (hRdef (by simpa [ctxAfter, hk_eq] using hkres))
              | some b' =>
                  have hk_side : (ctxAfter ctx resSide).regime.lookup? k' = some b' :=
                    hlookup_back k' b' hkres
                  have hb_eq : b = b' := by
                    have : some b = some b' := by
                      calc
                        some b = (ctxAfter ctx resSide).regime.lookup? k' := by symm; exact hreg
                        _ = some b' := hk_side
                    exact Option.some.inj this
                  exact congrArg some hb_eq.symm
            have hcons_res :
                (b = true → qtypPredHolds predSat θ qt μ (Value.num n)) ∧
                (b = false → ¬ qtypPredHolds predSat θ qt μ (Value.num n)) := by
              refine ⟨?_, ?_⟩
              · intro hb
                exact
                  qtypPredHolds_transport_pred
                    (predSat := predSat) (qt := qtSide) (qt' := qt)
                    (μ := μ) (v := Value.num n) hpred_eq (hcons.1 hb)
              · intro hb
                exact
                  qtypPredHolds_transport_pred_not
                    (predSat := predSat) (qt := qtSide) (qt' := qt)
                    (μ := μ) (v := Value.num n) hpred_eq (hcons.2 hb)
            exact
              locsRegime.withPred_ok (l, qt) k' arg_name pred_body var_env a n b
                hpred hreg_res hreal hmem hcons_res
  · intro x qt k hlookup hguard hRdef
    cases hkres : (ctxAfter ctx res).regime.lookup? k with
    | none =>
        exact False.elim (hRdef hkres)
    | some b =>
        have hRdef_side : (ctxAfter ctx resSide).regime.lookup? k ≠ none := by
          intro hnone
          have hk_side := hlookup_back k b hkres
          rw [hk_side] at hnone
          contradiction
        have hvar_side :=
          hcwr.2.1 x qt k
            (by simpa [ctxAfter] using hlookup)
            hguard
            hRdef_side
        exact
          varsRegime_transport_active_lookup_back
            (predSat := predSat)
            (R := (ctxAfter ctx resSide).regime)
            (R' := (ctxAfter ctx res).regime)
            (μ := μ) (ρ := ρ) (entry := (x, qt))
            hlookup_back hguard hkres hvar_side
  · intro x qt v hlookup hlookup_v
    have hcap_side :
        closureCapturedVarsRegime predSat
          (ctxAfter ctx resSide).regime
          qt μ θ v :=
      hcwr.2.2 x qt v
        (by simpa [ctxAfter] using hlookup)
        hlookup_v
    exact
      closureCapturedVarsRegime_transport_lookup_back
        (predSat := predSat)
        (R := (ctxAfter ctx resSide).regime)
        (R' := (ctxAfter ctx res).regime)
        (qt := qt) (μ := μ) (θ := θ) (v := v)
        hlookup_back hcap_side

private lemma consistentWithRegime_join_from_left
  (predSat : PredSat) (ctx : TypeContext)
  (resLeft resRight res : TypeResult)
  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (hmemEnv : res.memEnv' = joinMemEnvsStrong resLeft.memEnv' resRight.memEnv')
  (hregime : res.regime' = joinRegimes resLeft.regime' resRight.regime')
  (hcwr :
    consistentWithRegime predSat
      (ctxAfter ctx resLeft).regime
      (ctxAfter ctx resLeft) μ ρ θ) :
  consistentWithRegime predSat
    (ctxAfter ctx res).regime
    (ctxAfter ctx res) μ ρ θ :=
  consistentWithRegime_join_from_side
    predSat ctx resLeft resRight res resLeft μ ρ θ hmemEnv
    (by
      intro k b hk
      have hk' : (joinRegimes resLeft.regime' resRight.regime').lookup? k = some b := by
        simpa [ctxAfter, hregime] using hk
      simpa [ctxAfter] using
        joinRegimes_lookup_some_left resLeft.regime' resRight.regime' k b hk')
    (joinMemEnvsStrong_lookup_guardClosure_implies_left resLeft.memEnv' resRight.memEnv')
    hcwr

private lemma consistentWithRegime_join_from_right
  (predSat : PredSat) (ctx : TypeContext)
  (resLeft resRight res : TypeResult)
  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (hmemEnv : res.memEnv' = joinMemEnvsStrong resLeft.memEnv' resRight.memEnv')
  (hregime : res.regime' = joinRegimes resLeft.regime' resRight.regime')
  (hcwr :
    consistentWithRegime predSat
      (ctxAfter ctx resRight).regime
      (ctxAfter ctx resRight) μ ρ θ) :
  consistentWithRegime predSat
    (ctxAfter ctx res).regime
    (ctxAfter ctx res) μ ρ θ :=
  consistentWithRegime_join_from_side
    predSat ctx resLeft resRight res resRight μ ρ θ hmemEnv
    (by
      intro k b hk
      have hk' : (joinRegimes resLeft.regime' resRight.regime').lookup? k = some b := by
        simpa [ctxAfter, hregime] using hk
      simpa [ctxAfter] using
        joinRegimes_lookup_some_right resLeft.regime' resRight.regime' k b hk')
    (joinMemEnvsStrong_lookup_guardClosure_implies_right resLeft.memEnv' resRight.memEnv')
    hcwr

private lemma ite_join_transport_runtimeInstantiatesCtx
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

private lemma ite_qtypCleanUnder_lookup_true_back
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

private lemma ite_agreeValueUnder_clean_transport_by_lookupTrueBack
    {predSat : PredSat} {R R' : Regime}
    {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
    {qt : QTyp} {v₀ v₁ : Value}
    (hlookup_true_back : ∀ (k : Tag), R'.lookup? k = some true → R.lookup? k = some true)
    (hmemberVars₀_transport :
      ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
        MemberVarsRegimeEvidence predSat R μ₀ θ₀ σcap ρcap →
          MemberVarsRegimeEvidence predSat R' μ₀ θ₀ σcap ρcap)
    (hmemberCvcr₀_transport :
      ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
        MemberCvcrEvidence predSat R μ₀ θ₀ σcap ρcap →
          MemberCvcrEvidence predSat R' μ₀ θ₀ σcap ρcap)
    (hmemberVars₁_transport :
      ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
        MemberVarsRegimeEvidence predSat R μ₁ θ₁ σcap ρcap →
          MemberVarsRegimeEvidence predSat R' μ₁ θ₁ σcap ρcap)
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
    exact ite_qtypCleanUnder_lookup_true_back hlookup_true_back hclean'
  exact
    agreeValueUnder_clean_transport_by_cleanBack
      h_clean_back
      hmemberVars₀_transport hmemberCvcr₀_transport
      hmemberVars₁_transport hmemberCvcr₁_transport
      hclean hagree

private lemma ite_join_transport_agreeOnClean_from_member
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
      MemberVarsRegimeEvidence predSat src.regime' μ₀ θ₀ σcap ρcap →
        MemberVarsRegimeEvidence predSat res.regime' μ₀ θ₀ σcap ρcap)
  (hmemberCvcr₀_transport :
    ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
      MemberCvcrEvidence predSat src.regime' μ₀ θ₀ σcap ρcap →
        MemberCvcrEvidence predSat res.regime' μ₀ θ₀ σcap ρcap)
  (hmemberVars₁_transport :
    ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
      MemberVarsRegimeEvidence predSat src.regime' μ₁ θ₁ σcap ρcap →
        MemberVarsRegimeEvidence predSat res.regime' μ₁ θ₁ σcap ρcap)
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
            ite_agreeValueUnder_clean_transport_by_lookupTrueBack
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
          ite_agreeValueUnder_clean_transport_by_lookupTrueBack
            (predSat := predSat)
            (R := src.regime') (R' := res.regime')
            (μ₀ := μ₀) (μ₁ := μ₁) (θ₀ := θ₀) (θ₁ := θ₁)
            (qt := qt) (v₀ := v₀) (v₁ := v₁)
            hlookup_true_back
            hmemberVars₀_transport hmemberCvcr₀_transport
            hmemberVars₁_transport hmemberCvcr₁_transport
            hclean hagree
        exact agreeVarUnder.agree_values x qt v₀ v₁ hlookup₀ hlookup₁ hagree'

/-- Side-neutral skeleton for `consistentWithRegimeMasked_join_from_{left,right}`,
the masked counterpart of `consistentWithRegime_join_from_side`. Same two
divergence hypotheses (`hlookup_back`, `hguard_implies`) and `resSide` operand;
each conjunct additionally threads the `Or.inl masked | Or.inr …` alternative. -/
private lemma consistentWithRegimeMasked_join_from_side
  (masked : Tag → Prop) (predSat : PredSat) (ctx : TypeContext)
  (resLeft resRight res resSide : TypeResult)
  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (hmemEnv : res.memEnv' = joinMemEnvsStrong resLeft.memEnv' resRight.memEnv')
  (hlookup_back :
    ∀ k b, (ctxAfter ctx res).regime.lookup? k = some b →
      (ctxAfter ctx resSide).regime.lookup? k = some b)
  (hguard_implies :
    ∀ (l : Loc) (qt : QTyp) (k' : Tag) (arg_name : Name)
      (pred_body : PExpr) (var_env : CapturedVarEnv),
      (joinMemEnvsStrong resLeft.memEnv' resRight.memEnv').lookup l = some qt →
      qt.pred = Predicate.guardClosure k' arg_name pred_body var_env →
      ∃ qtSide, resSide.memEnv'.lookup l = some qtSide ∧
        qtSide.pred = Predicate.guardClosure k' arg_name pred_body var_env)
  (hcwr :
    consistentWithRegimeMasked masked predSat
      (ctxAfter ctx resSide).regime
      (ctxAfter ctx resSide) μ ρ θ) :
  consistentWithRegimeMasked masked predSat
    (ctxAfter ctx res).regime
    (ctxAfter ctx res) μ ρ θ := by
  rcases hcwr with ⟨hlocs, hvars, hclos⟩
  refine ⟨?_, ?_, ?_⟩
  · intro l qt k hlookup hguard hRdef
    cases hpred : qt.pred with
    | noPred =>
        simp [qtypGuardTag, hpred] at hguard
    | guardOnly k' =>
        exact Or.inr (locsRegime.guardOnly_ok (l, qt) k' hpred)
    | guardClosure k' arg_name pred_body var_env =>
        have hk_eq : k' = k := by
          have : some k' = some k := by
            calc
              some k' = qtypGuardTag qt := by simp [qtypGuardTag, hpred]
              _ = some k := hguard
          exact Option.some.inj this
        rcases
            hguard_implies l qt k' arg_name pred_body var_env
              (by simpa [ctxAfter, hmemEnv] using hlookup)
              hpred
          with ⟨qtSide, hlookupSide, hpredSide⟩
        have hRdef_side : (ctxAfter ctx resSide).regime.lookup? k' ≠ none := by
          intro hnone
          cases hkres : (ctxAfter ctx res).regime.lookup? k' with
          | none =>
              exact hRdef (by simpa [ctxAfter, hk_eq] using hkres)
          | some b =>
              have hk_side : (ctxAfter ctx resSide).regime.lookup? k' = some b :=
                hlookup_back k' b hkres
              rw [hk_side] at hnone
              contradiction
        have hguard_side : qtypGuardTag qtSide = some k' := by
          simp [qtypGuardTag, hpredSide]
        have hloc_side :=
          hlocs l qtSide k'
            (by simpa [ctxAfter] using hlookupSide)
            hguard_side
            hRdef_side
        rcases hloc_side with hmasked | hloc_side
        · exact Or.inl (by simpa [hk_eq] using hmasked)
        · cases hloc_side with
          | noPred_ok hnp =>
              simp [qtypGuardTag, hpredSide] at hnp
          | guardOnly_ok _ hgo =>
              simp [hpredSide] at hgo
          | withPred_ok kSide arg_name' pred_body' var_env' a n b hclos_side hreg hreal hmem hcons =>
              have hpred_ctor_eq :
                  Predicate.guardClosure kSide arg_name' pred_body' var_env' =
                    Predicate.guardClosure k' arg_name pred_body var_env := by
                calc
                  Predicate.guardClosure kSide arg_name' pred_body' var_env' = qtSide.pred := by
                    simpa using hclos_side.symm
                  _ = Predicate.guardClosure k' arg_name pred_body var_env := hpredSide
              cases hpred_ctor_eq
              have hpred_eq : qtSide.pred = qt.pred := by
                simp [hpredSide, hpred]
              have hreg_res : (ctxAfter ctx res).regime.lookup? k' = some b := by
                cases hkres : (ctxAfter ctx res).regime.lookup? k' with
                | none =>
                    exact False.elim (hRdef (by simpa [ctxAfter, hk_eq] using hkres))
                | some b' =>
                    have hk_side : (ctxAfter ctx resSide).regime.lookup? k' = some b' :=
                      hlookup_back k' b' hkres
                    have hb_eq : b = b' := by
                      have : some b = some b' := by
                        calc
                          some b = (ctxAfter ctx resSide).regime.lookup? k' := by symm; exact hreg
                          _ = some b' := hk_side
                      exact Option.some.inj this
                    exact congrArg some hb_eq.symm
              have hcons_res :
                  (b = true → qtypPredHolds predSat θ qt μ (Value.num n)) ∧
                  (b = false → ¬ qtypPredHolds predSat θ qt μ (Value.num n)) := by
                refine ⟨?_, ?_⟩
                · intro hb
                  exact
                    qtypPredHolds_transport_pred
                      (predSat := predSat) (qt := qtSide) (qt' := qt)
                      (μ := μ) (v := Value.num n) hpred_eq (hcons.1 hb)
                · intro hb
                  exact
                    qtypPredHolds_transport_pred_not
                      (predSat := predSat) (qt := qtSide) (qt' := qt)
                      (μ := μ) (v := Value.num n) hpred_eq (hcons.2 hb)
              exact Or.inr <|
                locsRegime.withPred_ok (l, qt) k' arg_name pred_body var_env a n b
                  hpred hreg_res hreal hmem hcons_res
  · intro x qt k hlookup hguard hRdef
    cases hkres : (ctxAfter ctx res).regime.lookup? k with
    | none =>
        exact Or.inr <| False.elim (hRdef hkres)
    | some b =>
        have hRdef_side : (ctxAfter ctx resSide).regime.lookup? k ≠ none := by
          intro hnone
          have hk_side := hlookup_back k b hkres
          rw [hk_side] at hnone
          contradiction
        have hvar_side :=
          hvars x qt k
            (by simpa [ctxAfter] using hlookup)
            hguard
            hRdef_side
        rcases hvar_side with hmasked | hvar_side
        · exact Or.inl hmasked
        · exact Or.inr <|
            varsRegime_transport_active_lookup_back
              (predSat := predSat)
              (R := (ctxAfter ctx resSide).regime)
              (R' := (ctxAfter ctx res).regime)
              (μ := μ) (ρ := ρ) (entry := (x, qt))
              hlookup_back hguard hkres hvar_side
  · intro x qt v hlookup hlookup_v
    have hcap_side :
        closureCapturedVarsRegimeMasked masked predSat
          (ctxAfter ctx resSide).regime
          qt μ θ v :=
      hclos x qt v
        (by simpa [ctxAfter] using hlookup)
        hlookup_v
    exact
      closureCapturedVarsRegimeMasked_transport_lookup_back
        (masked := masked) (predSat := predSat)
        (R := (ctxAfter ctx resSide).regime)
        (R' := (ctxAfter ctx res).regime)
        (qt := qt) (μ := μ) (θ := θ) (v := v)
        hlookup_back hcap_side

theorem consistentWithRegimeMasked_join_from_left
  (masked : Tag → Prop) (predSat : PredSat) (ctx : TypeContext)
  (resLeft resRight res : TypeResult)
  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (hmemEnv : res.memEnv' = joinMemEnvsStrong resLeft.memEnv' resRight.memEnv')
  (hregime : res.regime' = joinRegimes resLeft.regime' resRight.regime')
  (hcwr :
    consistentWithRegimeMasked masked predSat
      (ctxAfter ctx resLeft).regime
      (ctxAfter ctx resLeft) μ ρ θ) :
  consistentWithRegimeMasked masked predSat
    (ctxAfter ctx res).regime
    (ctxAfter ctx res) μ ρ θ :=
  consistentWithRegimeMasked_join_from_side
    masked predSat ctx resLeft resRight res resLeft μ ρ θ hmemEnv
    (by
      intro k b hk
      have hk' : (joinRegimes resLeft.regime' resRight.regime').lookup? k = some b := by
        simpa [ctxAfter, hregime] using hk
      simpa [ctxAfter] using
        joinRegimes_lookup_some_left resLeft.regime' resRight.regime' k b hk')
    (joinMemEnvsStrong_lookup_guardClosure_implies_left resLeft.memEnv' resRight.memEnv')
    hcwr

theorem consistentWithRegimeMasked_join_from_right
  (masked : Tag → Prop) (predSat : PredSat) (ctx : TypeContext)
  (resLeft resRight res : TypeResult)
  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (hmemEnv : res.memEnv' = joinMemEnvsStrong resLeft.memEnv' resRight.memEnv')
  (hregime : res.regime' = joinRegimes resLeft.regime' resRight.regime')
  (hcwr :
    consistentWithRegimeMasked masked predSat
      (ctxAfter ctx resRight).regime
      (ctxAfter ctx resRight) μ ρ θ) :
  consistentWithRegimeMasked masked predSat
    (ctxAfter ctx res).regime
    (ctxAfter ctx res) μ ρ θ :=
  consistentWithRegimeMasked_join_from_side
    masked predSat ctx resLeft resRight res resRight μ ρ θ hmemEnv
    (by
      intro k b hk
      have hk' : (joinRegimes resLeft.regime' resRight.regime').lookup? k = some b := by
        simpa [ctxAfter, hregime] using hk
      simpa [ctxAfter] using
        joinRegimes_lookup_some_right resLeft.regime' resRight.regime' k b hk')
    (joinMemEnvsStrong_lookup_guardClosure_implies_right resLeft.memEnv' resRight.memEnv')
    hcwr

/-- Successful `matchGuard` implies the returned guard tag appears as
    `qtypGuardTag` in the context's `varEnv` or `memEnv`. -/
private lemma guard_branch_alignment
    (predSat : PredSat) (tm : TagMeaning)
    (ctx : TypeContext) (μ₀ : Memory) (ρ₀ : VarEnv) (θ₀ : RealizationMap)
    (l₀ : Address) (pm₀ : Bool)
    (hwfTm : wfTagMeaningCtx tm ctx) (hpred : PredSatLaws predSat tm)
    (hcwr : consistentWithRegime predSat ctx.regime ctx μ₀ ρ₀ θ₀)
    (cond : Expr) (k : Tag) (deps : Deps) (b b' : Bool) (cfg' : Config)
    {fuel : Nat}
    (hric : runtimeInstantiatesCtx ctx μ₀ ρ₀ θ₀) :
    matchGuard cond ctx.memEnv ctx.varEnv fuel = .ok (k, deps) →
    ctx.regime.lookup? k = some b →
    terminatesTo cond
      { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀, registry := registry }
      cfg' (Value.bool b') →
    b' = b := by
  intro hmatch hregime hterm
  rcases hpred.match_iff cond ctx fuel k deps μ₀ ρ₀ θ₀ l₀ pm₀ registry cfg' b'
      hwfTm hmatch hric hterm with ⟨v, hv_owner, hmatch_iff_v⟩
  have hRdef : ctx.regime.lookup? k ≠ none := by
    simp [hregime]
  have hpred_implies_lookup_true : predSat k θ₀ μ₀ v → ctx.regime.lookup? k = some true := by
    intro hsat
    cases hv_owner with
    | inl hvar =>
        rcases hvar with ⟨x, qt, arg_name, pred_body, var_env, hlookup, hpred_qt, hvar⟩
        have htag_qt : qtypGuardTag qt = some k := by
          simp [qtypGuardTag, hpred_qt]
        have hvr : varsRegime predSat ctx.regime μ₀ θ₀ ρ₀ (x, qt) :=
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
              have hnot : ¬ qtypPredHolds predSat θ₀ qt μ₀ v1 := hconsist.2 hb1f
              have hsat1 : predSat k1 θ₀ μ₀ v1 := by
                simpa [hk, hv1] using hsat
              have hholds : qtypPredHolds predSat θ₀ qt μ₀ v1 :=
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
              have hnot : ¬ qtypPredHolds predSat θ₀ memQt μ₀ (Value.num n1) := hconsist.2 hb1f
              have hsat_num : predSat k1 θ₀ μ₀ (Value.num n1) := by
                simpa [hk, hv_num] using hsat
              have hholds : qtypPredHolds predSat θ₀ memQt μ₀ (Value.num n1) :=
                qtypPredHolds.guardClosure_ok hclos hsat_num
              exact False.elim (hnot hholds)
  have hlookup_true_implies_pred : ctx.regime.lookup? k = some true → predSat k θ₀ μ₀ v := by
    intro hktrue
    cases hv_owner with
    | inl hvar =>
        rcases hvar with ⟨x, qt, arg_name, pred_body, var_env, hlookup, hpred_qt, hvar⟩
        have htag_qt : qtypGuardTag qt = some k := by
          simp [qtypGuardTag, hpred_qt]
        have hvr : varsRegime predSat ctx.regime μ₀ θ₀ ρ₀ (x, qt) :=
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
            have hholds : qtypPredHolds predSat θ₀ qt μ₀ v1 := hconsist.1 hb1t
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
            have hholds : qtypPredHolds predSat θ₀ memQt μ₀ (Value.num n1) := hconsist.1 hb1t
            have hsat_num : predSat k1 θ₀ μ₀ (Value.num n1) := by
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
      have hsat : predSat k θ₀ μ₀ v := hmatch_iff_v.mp hb'true
      have hktrue : ctx.regime.lookup? k = some true := hpred_implies_lookup_true hsat
      have : some b = some true := by simpa [hregime] using hktrue
      exact Option.some.inj this
    · intro hbtrue
      have hktrue : ctx.regime.lookup? k = some true := by
        simp [hregime, hbtrue]
      have hsat : predSat k θ₀ μ₀ v := hlookup_true_implies_pred hktrue
      exact hmatch_iff_v.mpr hsat
  cases b <;> cases b' <;> simp at hb'_iff ⊢

/-- Public wrapper for branch-alignment from a successful `matchGuard`.
    Packages the runtime-owner extraction and the semantic alignment step
    needed by the single-run `ite` proof. -/
theorem matchGuard_runtime_branch_alignment
    (predSat : PredSat) (tm : TagMeaning)
    (ctx : TypeContext) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
    (a : Address) (pm : Bool)
    (hwfTm : wfTagMeaningCtx tm ctx) (hpred : PredSatLaws predSat tm)
    (hric : runtimeInstantiatesCtx ctx μ ρ θ)
    (hcwr : consistentWithRegime predSat ctx.regime ctx μ ρ θ)
    (cond : Expr) (k : Tag) (deps : Deps) (b b' : Bool) (cfg' : Config)
    {fuel : Nat}
    (hmatch : matchGuard cond ctx.memEnv ctx.varEnv fuel = .ok (k, deps))
    (hregime : ctx.regime.lookup? k = some b)
    (hterm : terminatesTo cond
      { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry }
      cfg' (Value.bool b')) :
    b' = b := by
  exact
    guard_branch_alignment predSat tm ctx μ ρ θ a pm
      hwfTm hpred hcwr cond k deps b b' cfg' hric hmatch hregime hterm

private lemma stepFR_ite_true
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 e3 : Expr) (fuel' : Nat) (res : TypeResult)
  (CanUse : Expr → Prop) (CtxReach : TypeContext → Prop)
  (hOp : RegistryOperationalSafe registry)
  (hctxPure : CtxReach { ctxᵢ with pureCtx := true })
  (hcan1 : CanUse e1) (hcan2 : CanUse e2)
  (IH :
    StepFR_IH_WithExprCtx predSat tm (Nat.succ (Nat.succ fuel'))
      CanUse CtxReach (registry := registry))
  (htc : typecheck ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) = .ok res)
  (k : Tag) (deps : Deps) (hmatch : matchGuard e1 ctxᵢ.memEnv ctxᵢ.varEnv fuel' = .ok (k, deps))
  (hregime_true : ctxᵢ.regime.lookup? k = some true)
  (res1 res2 : TypeResult)
  (htc1 : typecheckExpr { ctxᵢ with pureCtx := true } e1 fuel' = .ok res1)
  (_hbool : res1.qualType.etyp = ETyp.bool)
  (htc2 : let ctxTrue := { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩,
                                     nextTag := res1.nextTag',
                                     declaredExternRefs := res1.declared' }
          typecheckExpr ctxTrue e2 fuel' = .ok res2)
  (hctxTrue : CtxReach { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩,
                                   nextTag := res1.nextTag',
                                   declaredExternRefs := res1.declared' })
  (_res3 : TypeResult)
  (_htc3 : let ctxFalse := { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨false, deps⟩,
                                        nextLoc := res2.nextLoc', nextTag := res2.nextTag',
                                        declaredExternRefs := res2.declared' }
           typecheckExpr ctxFalse e3 fuel' = .ok _res3)
  (hmemEnv : res.memEnv' = res2.memEnv')
  (htagEnv : res.tagEnv' = res2.tagEnv')
  (hnextLoc : res.nextLoc' = max res2.nextLoc' _res3.nextLoc')
  (_hnextTag : res.nextTag' = max res2.nextTag' _res3.nextTag')
  (hregime' : res.regime' = res2.regime')
  (hdecl' : res.declared' = _res3.declared')
  (hpoison : res.qualType.poison = joinPoison ctxᵢ.pc res2.qualType.poison)
  (hetyp : res.qualType.etyp = res2.qualType.etyp)
  (hlog : res.tagLog' = res1.tagLog' ++ res2.tagLog' ++ _res3.tagLog') :
  StepFR ctxᵢ (Expr.ite e1 e2 e3) res predSat tm (Nat.succ (Nat.succ fuel')) (registry := registry) := by
  classical
  intro hpredlaws hframe hwfTm hTmBounded hfp μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁
    hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm
    hwfcfg₀ hwfcfg₁ hres₀ hres₁ hrd₀ hrd₁ ht₀ ht₁ P₀ P₁ hprem hroot₀ hroot₁
  have hframe' := hframe.of_log_eq hlog
  have hstruct₀ := terminatesTo_ite_inv' e1 e2 e3
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm, registry := registry } cf₀ o₀ ht₀
  rcases hstruct₀ with ⟨cfg₀1, b₀, ht₀_e1, hbranch₀, hpm₀1, hpm₀_final⟩
  have hstruct₁ := terminatesTo_ite_inv' e1 e2 e3
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm, registry := registry } cf₁ o₁ ht₁
  rcases hstruct₁ with ⟨cfg₁1, b₁, ht₁_e1, hbranch₁, hpm₁1, hpm₁_final⟩
  have htc1' : typecheck { ctxᵢ with pureCtx := true } e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have hwfTm_pure : wfTagMeaningCtx tm { ctxᵢ with pureCtx := true } := by
    simpa [wfTagMeaningCtx] using hwfTm
  have htagBounded_pure : TagBoundedCtx { ctxᵢ with pureCtx := true } := by
    simpa [TagBoundedCtx, tagEnvBoundedInCtx, predTagsBoundedInCtx, closureEnvBoundedInCtx] using htagBounded
  have hIH_e1 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 { ctxᵢ with pureCtx := true } hctxPure hcan1 hwfTm_pure htagBounded_pure res1 htc1'
  have hwf_pure : wfTypeContext { ctxᵢ with pureCtx := true } := by
    simp [wfTypeContext] at hwf ⊢
    exact hwf
  have hfp_pure : FootprintCtx tm { ctxᵢ with pureCtx := true } := hfp
  have hstep_e1 :=
    hIH_e1 hpredlaws hframe'.left.left hwfTm_pure hTmBounded hfp_pure μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 (Value.bool b₀) (Value.bool b₁)
      hθ₀ hθ₁ hwf_pure htagBounded_pure hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree
      a₀ a₁ pm hwfcfg₀ hwfcfg₁ hres₀ hres₁ hrd₀ hrd₁ ht₀_e1 ht₁_e1
      hprem (hprem.run₀.closed hroot₀ (SubStep.iteCondPure (f := fuel') hmatch hregime_true))
      (hprem.run₁.closed hroot₁ (SubStep.iteCondPure (f := fuel') hmatch hregime_true))
  rcases hstep_e1 with ⟨_tm1, _hcanon1, _hpredlaws1, _hresTm1, hstep_e1⟩
  rcases hstep_e1 with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, _hvtyp₀1, _hvtyp₁1,
    _hwfTm1, hwf1, _htagBounded1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1,
    hcwr₀1, hcwr₁1, hagree1, _hvalc₀1, _hvalc₁1, hres_agree1, _hrd₀1, _hrd₁1, hM₀1, hM₁1, hF₀1, hF₁1⟩
  have hb₀_true : b₀ = true := by
    exact
      guard_branch_alignment predSat tm
        ctxᵢ μ₀ ρ₀ θ₀ a₀ pm
        hwfTm hpredlaws hcwr₀
        e1 k deps true b₀ cfg₀1
        hric₀
        hmatch hregime_true ht₀_e1
  have hb₁_true : b₁ = true := by
    exact
      guard_branch_alignment predSat tm
        ctxᵢ μ₁ ρ₁ θ₁ a₁ pm
        hwfTm hpredlaws hcwr₁
        e1 k deps true b₁ cfg₁1
        hric₁
        hmatch hregime_true ht₁_e1
  have ht₀_e2 : terminatesTo e2 cfg₀1 cf₀ o₀ := by
    cases hbranch₀ with
    | inl h => exact h.2
    | inr h =>
        have : false = true := by rw [← h.1, hb₀_true]
        contradiction
  have ht₁_e2 : terminatesTo e2 cfg₁1 cf₁ o₁ := by
    cases hbranch₁ with
    | inl h => exact h.2
    | inr h =>
        have : false = true := by rw [← h.1, hb₁_true]
        contradiction
  let ctxTrue := { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩,
                             nextTag := res1.nextTag',
                             declaredExternRefs := res1.declared' }
  have htc2' : typecheck ctxTrue e2 fuel' = .ok res2 := by
    simpa [typecheck, Nat.succ_sub_one] using htc2
  have hwfTm_true : wfTagMeaningCtx tm ctxTrue := by
    simpa [wfTagMeaningCtx, ctxTrue] using hwfTm
  have hb1 : ctxᵢ.nextTag ≤ res1.nextTag' :=
    typecheck_nextTag_mono { ctxᵢ with pureCtx := true } e1 fuel' res1 htc1
  have htagBounded_true : TagBoundedCtx ctxTrue := by
    obtain ⟨hb_tag, ⟨hb_predV, hb_predM⟩, hb_clos⟩ := htagBounded
    have hk_lt := matchGuard_tag_bounded e1 ctxᵢ.memEnv ctxᵢ.varEnv fuel' k deps ctxᵢ.nextTag hmatch hb_predV hb_predM
    exact ⟨tagEnvBounded_mono _ _ _ (tagEnvBounded_insert_of_lt ctxᵢ.tagEnv ctxᵢ.nextTag k _ hb_tag hk_lt) hb1,
      ⟨predTagsBoundedInVarEnv_mono hb_predV hb1, predTagsBoundedInMemEnv_mono hb_predM hb1⟩,
      varEnvClosuresCapturedBounded_mono hb_clos hb1⟩
  have hTmBounded_true : TagMeaningBounded tm ctxTrue.nextTag := hTmBounded.mono hb1
  have hfp_true : FootprintCtx tm ctxTrue :=
    ⟨RecordsCover.matched (b := true) hwfTm hfp.1 hmatch, hfp.2⟩
  have hIH_e2 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e2 ctxTrue (by simpa [ctxTrue] using hctxTrue) hcan2 hwfTm_true htagBounded_true res2 htc2'
  have htcIf : typecheckIf ctxᵢ e1 e2 e3 (Nat.succ fuel') = .ok res := by
    simpa [typecheck, typecheckExpr_ite_succ] using htc
  have hpredNo : res.qualType.pred = Predicate.noPred :=
    typecheckIf_pred_noPred ctxᵢ e1 e2 e3 (Nat.succ fuel') res htcIf
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
    exact tagEnvConsistentWithRegime_insert_true
        ctxᵢ.tagEnv ctxᵢ.regime k deps htagR hregime_true
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
          MemberVarsRegimeEvidence predSat res1.regime' cfg₀1.memory θ₀1 σcap ρcap →
            MemberVarsRegimeEvidence predSat ctxTrue.regime cfg₀1.memory θ₀1 σcap ρcap := by
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
          MemberVarsRegimeEvidence predSat res1.regime' cfg₁1.memory θ₁1 σcap ρcap →
            MemberVarsRegimeEvidence predSat ctxTrue.regime cfg₁1.memory θ₁1 σcap ρcap := by
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
          pureMode := cfg₀1.pureMode, registry := registry } := by
    have hreg_cfg₁1_local : cfg₁1.registry = registry := by
      simpa using terminatesTo_preserves_registry ht₁_e1
    cases cfg₁1 with
    | mk m v n pm r =>
      simp only [Config.mk.injEq, true_and]
      refine ⟨hpm_eq, ?_⟩
      simpa using hreg_cfg₁1_local
  have ht₁_e2' : terminatesTo e2
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr,
        pureMode := cfg₀1.pureMode, registry := registry }
      cf₁ o₁ := by
    rw [← hcfg₁1_eq]
    exact ht₁_e2
  have hwfcf₁1' : wfConfig
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr,
        pureMode := cfg₀1.pureMode, registry := registry } := by
    rw [← hcfg₁1_eq]
    exact hwfcf₁1
  -- Thread extern registry for cfg₀1 so ht₀_e2 matches the IH's expected config.
  have hreg_cfg₀1 : cfg₀1.registry = registry := by
    simpa using terminatesTo_preserves_registry ht₀_e1
  have hcfg₀1_eq : cfg₀1 = { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry } :=
    config_eq_of_registry cfg₀1 registry hreg_cfg₀1
  have ht₀_e2' : terminatesTo e2 { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry } cf₀ o₀ := by
    rw [← hcfg₀1_eq]; exact ht₀_e2
  have hwfcf₀1' : wfConfig { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry } := by
    rw [← hcfg₀1_eq]; exact hwfcf₀1
  -- Thread RegistryReservedWF and ReservedDiscipline through e1 evaluation for e2's IH
  have hres₀1 : RegistryReservedWF registry cfg₀1.memory cfg₀1.nextAddr := by
    apply RegistryReservedWF_mono hres₀
    · exact terminatesTo_memory_contains_mono e1
        { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm, registry := registry }
        cfg₀1 (Value.bool b₀) hOp ht₀_e1
    · exact terminatesTo_nextAddr_mono e1
        { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm, registry := registry }
        cfg₀1 (Value.bool b₀) hOp ht₀_e1
  have hres₁1 : RegistryReservedWF registry cfg₁1.memory cfg₁1.nextAddr := by
    apply RegistryReservedWF_mono hres₁
    · exact terminatesTo_memory_contains_mono e1
        { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm, registry := registry }
        cfg₁1 (Value.bool b₁) hOp ht₁_e1
    · exact terminatesTo_nextAddr_mono e1
        { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm, registry := registry }
        cfg₁1 (Value.bool b₁) hOp ht₁_e1
  have hrd₀1' : ReservedDiscipline registry ctxTrue.declaredExternRefs θ₀1 := by
    simp only [ctxTrue]; simpa [hreg_cfg₀1] using _hrd₀1
  have hrd₁1' : ReservedDiscipline registry ctxTrue.declaredExternRefs θ₁1 := by
    have hreg₁1 : cfg₁1.registry = registry := by simpa using terminatesTo_preserves_registry ht₁_e1
    simp only [ctxTrue]; simpa [hreg₁1] using _hrd₁1
  have hroot₀2 : P₀ ⟨ctxTrue, e2, fuel',
      { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry }⟩ := by
    rw [← hcfg₀1_eq]
    exact hprem.run₀.closed hroot₀ (SubStep.iteThenMatched (f := fuel') hmatch hregime_true htc1
      (by simpa [hb₀_true] using ht₀_e1))
  have hroot₁2 : P₁ ⟨ctxTrue, e2, fuel',
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry }⟩ := by
    rw [← hcfg₁1_eq]
    exact hprem.run₁.closed hroot₁ (SubStep.iteThenMatched (f := fuel') hmatch hregime_true htc1
      (by simpa [hb₁_true] using ht₁_e1))
  have hstep_e2 :=
    hIH_e2 hpredlaws hframe'.left.right hwfTm_true hTmBounded_true hfp_true
      cfg₀1.memory cfg₁1.memory cfg₀1.varEnv cfg₁1.varEnv θ₀1 θ₁1
      cf₀ cf₁ o₀ o₁
      hθ₀1wf hθ₁1wf hwf_true htagBounded_true hric₀1' hric₁1' htagR_true
      hcwr₀1' hcwr₁1' hagree1'
      cfg₀1.nextAddr cfg₁1.nextAddr cfg₀1.pureMode hwfcf₀1' hwfcf₁1'
      hres₀1 hres₁1 hrd₀1' hrd₁1' ht₀_e2' ht₁_e2' hprem hroot₀2 hroot₁2
  rcases hstep_e2 with ⟨tm2, hcanon2, hpredlaws2, hresTm2, hstep_e2⟩
  rcases hstep_e2 with
    ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, _hvtyp₀2, _hvtyp₁2, _hTm2, hwf2, _htagBounded2, hwfcf₀2, hwfcf₁2,
      hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree2, _hvalc₀2, _hvalc₁2, hres_agree2, _hrd₀2, _hrd₁2, hM₀2, hM₁2, hF₀2, hF₁2⟩
  have hθext₀ : wfExtendsMap θ₀ θ₀2 := wfExtendsMap_trans hθext₀1 hθext₀2
  have hθext₁ : wfExtendsMap θ₁ θ₁2 := wfExtendsMap_trans hθext₁1 hθext₁2
  -- ctxAfter fields: memEnv, tagEnv, varEnv, regime match; nextLoc/nextTag are max-based (≥ res2's)
  have hctxAfter_memEnv : (ctxAfter ctxᵢ res).memEnv = (ctxAfter ctxTrue res2).memEnv := by
    simp [ctxAfter, hmemEnv]
  have hctxAfter_tagEnv : (ctxAfter ctxᵢ res).tagEnv = (ctxAfter ctxTrue res2).tagEnv := by
    simp [ctxAfter, htagEnv]
  have hctxAfter_varEnv : (ctxAfter ctxᵢ res).varEnv = (ctxAfter ctxTrue res2).varEnv := by
    simp [ctxAfter, ctxTrue]
  have hctxAfter_regime : (ctxAfter ctxᵢ res).regime = (ctxAfter ctxTrue res2).regime := by
    simp [ctxAfter, hregime']
  -- Footprint bookkeeping: compose the condition run and the then-branch run.
  have hRback : ∀ k' d, tm.lookup k' = some d → (ctxAfter ctxTrue res2).regime.lookup? k' ≠ none →
      (ctxAfter { ctxᵢ with pureCtx := true } res1).regime.lookup? k' ≠ none := by
    intro k' d hd hk'
    have h := regime_defined_back (regime_monotoneExt ctxTrue e2 fuel' res2 htc2')
      hTmBounded_true k' d hd (by simpa [ctxAfter] using hk')
    rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
    cases hl : ctxTrue.regime.lookup? k' with
    | none => exact absurd hl h
    | some b =>
        have hb := typecheckExpr_pure_regime_bridge_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1 k' b (by simpa [ctxTrue] using hl)
        simp [ctxAfter, hb]
  have hM₀_case : MapKeepsBelow ctxᵢ.nextLoc θ₀ θ₀2 := hM₀1.trans hM₀2 (Nat.le_refl _)
  have hM₁_case : MapKeepsBelow ctxᵢ.nextLoc θ₁ θ₁2 := hM₁1.trans hM₁2 (Nat.le_refl _)
  have hF₀_case : KeepsFootprints tm (ctxAfter ctxᵢ res).regime θ₀ μ₀ cf₀.memory := by
    rw [hctxAfter_regime]
    exact KeepsFootprints.trans hF₀1 hF₀2 (TagMeaningExtends.refl tm) hθext₀1.1 hRback
  have hF₁_case : KeepsFootprints tm (ctxAfter ctxᵢ res).regime θ₁ μ₁ cf₁.memory := by
    rw [hctxAfter_regime]
    exact KeepsFootprints.trans hF₁1 hF₁2 (TagMeaningExtends.refl tm) hθext₁1.1 hRback
  have hric₀_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
    simp only [runtimeInstantiatesCtx, hctxAfter_memEnv, hctxAfter_varEnv]
    exact hric₀2
  have hric₁_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
    simp only [runtimeInstantiatesCtx, hctxAfter_memEnv, hctxAfter_varEnv]
    exact hric₁2
  have htag_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) := by
    simp only [regimeConsistentWithCtx, ctxAfter, htagEnv, hregime']
    exact htagR2
  have hcwr₀_final :
      consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf₀.memory cf₀.varEnv θ₀2 := by
    simp only [consistentWithRegime, hctxAfter_regime, hctxAfter_memEnv, hctxAfter_varEnv]
    exact hcwr₀2
  have hcwr₁_final :
      consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf₁.memory cf₁.varEnv θ₁2 := by
    simp only [consistentWithRegime, hctxAfter_regime, hctxAfter_memEnv, hctxAfter_varEnv]
    exact hcwr₁2
  have hagree_final :
      agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁2 := by
    simp only [agreeOnClean, hctxAfter_regime, hctxAfter_memEnv, hctxAfter_varEnv]
    exact hagree2
  have hresTm : QTypRespectsTagMeaning tm2 res.qualType := by
    have hguard : qtypGuardDesc? res.qualType = none := by
      simp [qtypGuardDesc?, hpredNo]
    intro qt' k' d hinq hqd
    exact
      (QTypRespectsTagMeaning_transport_etyp_noGuard
        tm2 res2.qualType res.qualType hresTm2 hetyp hguard) hinq hqd
  have hTm_final : wfTagMeaningCtx tm2 (ctxAfter ctxᵢ res) := by
    simp only [wfTagMeaningCtx] at _hTm2 ⊢
    rwa [hctxAfter_varEnv, hctxAfter_memEnv]
  have hboundary_ite : BoundaryTagMeaningPost ctxᵢ res predSat tm tm2 := by
    exact ⟨hcanon2.1, by rw [_hnextTag]; exact hcanon2.2.1.mono (Nat.le_max_left _ _),
      hTm_final, hresTm, hpredlaws2,
      hcanon2.within.mono_log (fun a ha => by rw [hlog]; simp [ha])⟩
  refine ⟨tm2, hboundary_ite, hpredlaws2, hresTm, ?_⟩
  refine ⟨θ₀2, θ₁2, hθext₀, hθext₁, ?_, ?_, ?_, ?_, ?_, hwfcf₀2, hwfcf₁2,
    hric₀_final, hric₁_final, htag_final, hcwr₀_final, hcwr₁_final, hagree_final,
    ?_, ?_, ?_, ?_, ?_, hM₀_case, hM₁_case, hF₀_case, hF₁_case⟩
  · simpa [hetyp] using _hvtyp₀2
  · simpa [hetyp] using _hvtyp₁2
  · exact hTm_final
  · -- wfTypeContext: depends on memEnv and nextLoc (monotone in nextLoc)
    simp only [wfTypeContext, ctxAfter, hnextLoc]
    refine ⟨?_, varEnvRefLocsBounded_mono hwf2.2.1 (by simp [ctxAfter]),
             varEnvClosuresCapturedRefLocsBounded_mono hwf2.2.2 (by simp [ctxAfter])⟩
    intro l hl
    rw [hmemEnv] at hl
    exact Nat.lt_of_lt_of_le (hwf2.1 l (by simpa [ctxAfter] using hl)) (Nat.le_max_left _ _)
  · -- TagBoundedCtx (ctxAfter ctxᵢ res)
    exact typecheckExpr_preserves_TagBoundedCtx ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res (by simpa [typecheck] using htc) htagBounded
  · refine valueConsistentWithRegime.noTag (predSat := predSat) (R := (ctxAfter ctxᵢ res).regime)
      (qt := res.qualType) (μ := cf₀.memory) (v := o₀) ?_ ?_
    · simp [qtypGuardTag, hpredNo]
    · have hcap₂ : closureCapturedVarsRegime predSat (ctxAfter ctxTrue res2).regime res2.qualType cf₀.memory θ₀2 o₀ :=
        valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₀2
      have hcap₂' : closureCapturedVarsRegime predSat (ctxAfter ctxᵢ res).regime res2.qualType cf₀.memory θ₀2 o₀ := by
        rwa [hctxAfter_regime]
      exact closureCapturedVarsRegime_transport_etyp hetyp.symm hcap₂'
  · refine valueConsistentWithRegime.noTag (predSat := predSat) (R := (ctxAfter ctxᵢ res).regime)
      (qt := res.qualType) (μ := cf₁.memory) (v := o₁) ?_ ?_
    · simp [qtypGuardTag, hpredNo]
    · have hcap₂ : closureCapturedVarsRegime predSat (ctxAfter ctxTrue res2).regime res2.qualType cf₁.memory θ₁2 o₁ :=
        valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₁2
      have hcap₂' : closureCapturedVarsRegime predSat (ctxAfter ctxᵢ res).regime res2.qualType cf₁.memory θ₁2 o₁ := by
        rwa [hctxAfter_regime]
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
      rw [hctxAfter_regime]; exact hres_agree2
    have hagree2' :
        agreeValueUnder predSat (ctxAfter ctxᵢ res).regime
          cf₀.memory cf₁.memory θ₀2 θ₁2 res2.qualType o₀ o₁ :=
      hres_agree2' hclean2
    exact agreeValueUnder_transport_clean hclean hetyp hpoison_imp hagree2'
  · -- ReservedDiscipline for θ₀2: e3's (unexecuted) typechecking only grows the
    -- declared set, so lift the e2-run discipline along that inclusion.
    rw [hdecl']
    exact ReservedDiscipline.mono_declared
      (fun id h => typecheck_declared'_mono _ e3 fuel' _res3 (by simpa [typecheck] using _htc3) id h)
      _hrd₀2
  · -- ReservedDiscipline for θ₁2: same lift
    rw [hdecl']
    exact ReservedDiscipline.mono_declared
      (fun id h => typecheck_declared'_mono _ e3 fuel' _res3 (by simpa [typecheck] using _htc3) id h)
      _hrd₁2

-- Known false case: R(k) = some false (else-branch effective)
private lemma stepFR_ite_false
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 e3 : Expr) (fuel' : Nat) (res : TypeResult)
  (CanUse : Expr → Prop) (CtxReach : TypeContext → Prop)
  (hOp : RegistryOperationalSafe registry)
  (hctxPure : CtxReach { ctxᵢ with pureCtx := true })
  (hcan1 : CanUse e1) (hcan3 : CanUse e3)
  (IH :
    StepFR_IH_WithExprCtx predSat tm (Nat.succ (Nat.succ fuel'))
      CanUse CtxReach (registry := registry))
  (htc : typecheck ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) = .ok res)
  (k : Tag) (deps : Deps) (hmatch : matchGuard e1 ctxᵢ.memEnv ctxᵢ.varEnv fuel' = .ok (k, deps))
  (hregime_false : ctxᵢ.regime.lookup? k = some false)
  (res1 : TypeResult)
  (htc1 : typecheckExpr { ctxᵢ with pureCtx := true } e1 fuel' = .ok res1)
  (_hbool : res1.qualType.etyp = ETyp.bool)
  (_res2 : TypeResult)
  (_htc2 : let ctxTrue := { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩,
                                      nextTag := res1.nextTag',
                                      declaredExternRefs := res1.declared' }
           typecheckExpr ctxTrue e2 fuel' = .ok _res2)
  (res3 : TypeResult)
  (htc3 : let ctxFalse := { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨false, deps⟩,
                                       nextLoc := _res2.nextLoc', nextTag := _res2.nextTag',
                                       declaredExternRefs := _res2.declared' }
          typecheckExpr ctxFalse e3 fuel' = .ok res3)
  (hctxFalse : CtxReach { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨false, deps⟩,
                                     nextLoc := _res2.nextLoc', nextTag := _res2.nextTag',
                                     declaredExternRefs := _res2.declared' })
  (hmemEnv : res.memEnv' = res3.memEnv')
  (htagEnv : res.tagEnv' = res3.tagEnv')
  (hnextLoc : res.nextLoc' = max _res2.nextLoc' res3.nextLoc')
  (_hnextTag : res.nextTag' = max _res2.nextTag' res3.nextTag')
  (hregime' : res.regime' = res3.regime')
  (hdecl' : res.declared' = res3.declared')
  (hpoison : res.qualType.poison = joinPoison ctxᵢ.pc res3.qualType.poison)
  (hetyp : res.qualType.etyp = res3.qualType.etyp)
  (hlog : res.tagLog' = res1.tagLog' ++ _res2.tagLog' ++ res3.tagLog') :
  StepFR ctxᵢ (Expr.ite e1 e2 e3) res predSat tm (Nat.succ (Nat.succ fuel')) (registry := registry) := by
  classical
  intro hpredlaws hframe hwfTm hTmBounded hfp μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁
    hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm
    hwfcfg₀ hwfcfg₁ hres₀ hres₁ hrd₀ hrd₁ ht₀ ht₁ P₀ P₁ hprem hroot₀ hroot₁
  have hframe' := hframe.of_log_eq hlog
  have hstruct₀ := terminatesTo_ite_inv' e1 e2 e3
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm, registry := registry } cf₀ o₀ ht₀
  rcases hstruct₀ with ⟨cfg₀1, b₀, ht₀_e1, hbranch₀, hpm₀1, hpm₀_final⟩
  have hstruct₁ := terminatesTo_ite_inv' e1 e2 e3
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm, registry := registry } cf₁ o₁ ht₁
  rcases hstruct₁ with ⟨cfg₁1, b₁, ht₁_e1, hbranch₁, hpm₁1, hpm₁_final⟩
  have htc1' : typecheck { ctxᵢ with pureCtx := true } e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have hwfTm_pure : wfTagMeaningCtx tm { ctxᵢ with pureCtx := true } := by
    simpa [wfTagMeaningCtx] using hwfTm
  have htagBounded_pure : TagBoundedCtx { ctxᵢ with pureCtx := true } := by
    simpa [TagBoundedCtx, tagEnvBoundedInCtx, predTagsBoundedInCtx, closureEnvBoundedInCtx] using htagBounded
  have hIH_e1 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 { ctxᵢ with pureCtx := true } hctxPure hcan1 hwfTm_pure htagBounded_pure res1 htc1'
  have hwf_pure : wfTypeContext { ctxᵢ with pureCtx := true } := by
    simp [wfTypeContext] at hwf ⊢
    exact hwf
  have hfp_pure : FootprintCtx tm { ctxᵢ with pureCtx := true } := hfp
  have hstep_e1 :=
    hIH_e1 hpredlaws hframe'.left.left hwfTm_pure hTmBounded hfp_pure μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 (Value.bool b₀) (Value.bool b₁)
      hθ₀ hθ₁ hwf_pure htagBounded_pure hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree
      a₀ a₁ pm hwfcfg₀ hwfcfg₁ hres₀ hres₁ hrd₀ hrd₁ ht₀_e1 ht₁_e1
      hprem (hprem.run₀.closed hroot₀ (SubStep.iteCondPure (f := fuel') hmatch hregime_false))
      (hprem.run₁.closed hroot₁ (SubStep.iteCondPure (f := fuel') hmatch hregime_false))
  rcases hstep_e1 with ⟨_tm1, _hcanon1, _hpredlaws1, _hresTm1, hstep_e1⟩
  rcases hstep_e1 with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, _hvtyp₀1, _hvtyp₁1,
    _hwfTm1, hwf1, _htagBounded1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1,
    hcwr₀1, hcwr₁1, hagree1, _hvalc₀1, _hvalc₁1, hres_agree1, _hrd₀1, _hrd₁1, hM₀1, hM₁1, hF₀1, hF₁1⟩
  have hb₀_false : b₀ = false := by
    exact
      guard_branch_alignment predSat tm
        ctxᵢ μ₀ ρ₀ θ₀ a₀ pm
        hwfTm hpredlaws hcwr₀
        e1 k deps false b₀ cfg₀1
        hric₀
        hmatch hregime_false ht₀_e1
  have hb₁_false : b₁ = false := by
    exact
      guard_branch_alignment predSat tm
        ctxᵢ μ₁ ρ₁ θ₁ a₁ pm
        hwfTm hpredlaws hcwr₁
        e1 k deps false b₁ cfg₁1
        hric₁
        hmatch hregime_false ht₁_e1
  have ht₀_e3 : terminatesTo e3 cfg₀1 cf₀ o₀ := by
    cases hbranch₀ with
    | inl h =>
        have : true = false := by rw [← h.1, hb₀_false]
        contradiction
    | inr h => exact h.2
  have ht₁_e3 : terminatesTo e3 cfg₁1 cf₁ o₁ := by
    cases hbranch₁ with
    | inl h =>
        have : true = false := by rw [← h.1, hb₁_false]
        contradiction
    | inr h => exact h.2
  let ctxFalse := { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨false, deps⟩,
                              declaredExternRefs := res1.declared' }
  let ctxFalse' := { ctxFalse with nextLoc := _res2.nextLoc', nextTag := _res2.nextTag',
                                   declaredExternRefs := _res2.declared' }
  have htc3' : typecheck ctxFalse' e3 fuel' = .ok res3 := by
    simpa [typecheck, Nat.succ_sub_one, ctxFalse', ctxFalse] using htc3
  have hwfTm_false : wfTagMeaningCtx tm ctxFalse' := by
    simpa [wfTagMeaningCtx, ctxFalse', ctxFalse] using hwfTm
  have htagBounded_false : TagBoundedCtx ctxFalse' := by
    obtain ⟨hb_tag, ⟨hb_predV, hb_predM⟩, hb_clos⟩ := htagBounded
    have hk_lt := matchGuard_tag_bounded e1 ctxᵢ.memEnv ctxᵢ.varEnv fuel' k deps ctxᵢ.nextTag hmatch hb_predV hb_predM
    have hmono : ctxᵢ.nextTag ≤ _res2.nextTag' :=
      Nat.le_trans (typecheck_nextTag_mono { ctxᵢ with pureCtx := true } e1 fuel' res1 htc1)
        (typecheck_normal_nextTag_mono
          { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩,
                      nextTag := res1.nextTag',
                      declaredExternRefs := res1.declared' } e2 fuel' _res2
          (show typecheck _ e2 _ = _ from _htc2))
    refine ⟨?_, ⟨predTagsBoundedInVarEnv_mono hb_predV hmono, predTagsBoundedInMemEnv_mono hb_predM hmono⟩,
            varEnvClosuresCapturedBounded_mono hb_clos hmono⟩
    exact tagEnvBounded_insert_of_lt ctxᵢ.tagEnv _res2.nextTag' k _ (fun j hj => Nat.lt_of_lt_of_le (hb_tag j hj) hmono) (Nat.lt_of_lt_of_le hk_lt hmono)
  have hTmBounded_false : TagMeaningBounded tm ctxFalse'.nextTag := by
    have hmono : ctxᵢ.nextTag ≤ _res2.nextTag' :=
      Nat.le_trans (typecheck_nextTag_mono { ctxᵢ with pureCtx := true } e1 fuel' res1 htc1)
        (typecheck_normal_nextTag_mono
          { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩,
                      nextTag := res1.nextTag',
                      declaredExternRefs := res1.declared' } e2 fuel' _res2
          (show typecheck _ e2 _ = _ from _htc2))
    simpa [ctxFalse', ctxFalse] using hTmBounded.mono hmono
  have hle_nl : ctxᵢ.nextLoc ≤ ctxFalse'.nextLoc := by
    have htc2_tc : typecheck { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩,
                                         nextTag := res1.nextTag',
                                         declaredExternRefs := res1.declared' } e2 fuel' = .ok _res2 := by
      simpa [typecheck] using _htc2
    exact typecheck_nextLoc_mono { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩,
                                             nextTag := res1.nextTag',
                                             declaredExternRefs := res1.declared' } e2 fuel' _res2 htc2_tc
  have hfp_false : FootprintCtx tm ctxFalse' :=
    ⟨RecordsCover.matched (b := false) hwfTm hfp.1 hmatch,
     fun k' d hd l hl => Nat.lt_of_lt_of_le (hfp.2 k' d hd l hl) hle_nl⟩
  have hIH_e3 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e3 ctxFalse' (by simpa [ctxFalse', ctxFalse] using hctxFalse)
      hcan3 hwfTm_false htagBounded_false res3 htc3'
  have htcIf : typecheckIf ctxᵢ e1 e2 e3 (Nat.succ fuel') = .ok res := by
    simpa [typecheck, typecheckExpr_ite_succ] using htc
  have hpredNo : res.qualType.pred = Predicate.noPred :=
    typecheckIf_pred_noPred ctxᵢ e1 e2 e3 (Nat.succ fuel') res htcIf
  have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀
  have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁
  have hwf_false : wfTypeContext ctxFalse := by
    simpa [wfTypeContext, ctxFalse] using hwf
  have hwf_false' : wfTypeContext ctxFalse' := by
    simp only [wfTypeContext, ctxFalse', ctxFalse]
    have hle : ctxᵢ.nextLoc ≤ _res2.nextLoc' := by
      have htc2_tc : typecheck { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩,
                                           nextTag := res1.nextTag',
                                           declaredExternRefs := res1.declared' } e2 fuel' = .ok _res2 := by
        simpa [typecheck] using _htc2
      have := typecheck_nextLoc_mono { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩,
                                                 nextTag := res1.nextTag',
                                                 declaredExternRefs := res1.declared' } e2 fuel' _res2 htc2_tc
      simpa using this
    exact ⟨fun l hl => Nat.lt_of_lt_of_le (hwf_false.1 l hl) hle,
           varEnvRefLocsBounded_mono hwf_false.2.1 hle,
           varEnvClosuresCapturedRefLocsBounded_mono hwf_false.2.2 hle⟩
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
    exact tagEnvConsistentWithRegime_insert_false
        ctxᵢ.tagEnv ctxᵢ.regime k deps htagR
  have htagR_false' : regimeConsistentWithCtx ctxFalse' := by
    simp only [regimeConsistentWithCtx, ctxFalse', ctxFalse]
    exact htagR_false
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
          MemberVarsRegimeEvidence predSat res1.regime' cfg₀1.memory θ₀1 σcap ρcap →
            MemberVarsRegimeEvidence predSat ctxFalse.regime cfg₀1.memory θ₀1 σcap ρcap := by
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
          MemberVarsRegimeEvidence predSat res1.regime' cfg₁1.memory θ₁1 σcap ρcap →
            MemberVarsRegimeEvidence predSat ctxFalse.regime cfg₁1.memory θ₁1 σcap ρcap := by
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
          pureMode := cfg₀1.pureMode, registry := registry } := by
    have hreg_cfg₁1_local : cfg₁1.registry = registry := by
      simpa using terminatesTo_preserves_registry ht₁_e1
    cases cfg₁1 with
    | mk m v n pm r =>
      simp only [Config.mk.injEq, true_and]
      refine ⟨hpm_eq, ?_⟩
      simpa using hreg_cfg₁1_local
  have ht₁_e3' : terminatesTo e3
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr,
        pureMode := cfg₀1.pureMode, registry := registry }
      cf₁ o₁ := by
    rw [← hcfg₁1_eq]
    exact ht₁_e3
  have hwfcf₁1' : wfConfig
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr,
        pureMode := cfg₀1.pureMode, registry := registry } := by
    rw [← hcfg₁1_eq]
    exact hwfcf₁1
  -- Transfer properties from ctxFalse to ctxFalse' (only nextLoc/nextTag differ)
  have hric₀1'_f : runtimeInstantiatesCtx ctxFalse' cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    simp only [runtimeInstantiatesCtx, ctxFalse', ctxFalse] at hric₀1' ⊢; exact hric₀1'
  have hric₁1'_f : runtimeInstantiatesCtx ctxFalse' cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simp only [runtimeInstantiatesCtx, ctxFalse', ctxFalse] at hric₁1' ⊢; exact hric₁1'
  have hcwr₀1'_f : consistentWithRegime predSat ctxFalse'.regime ctxFalse' cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    simp only [consistentWithRegime, ctxFalse', ctxFalse] at hcwr₀1' ⊢; exact hcwr₀1'
  have hcwr₁1'_f : consistentWithRegime predSat ctxFalse'.regime ctxFalse' cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simp only [consistentWithRegime, ctxFalse', ctxFalse] at hcwr₁1' ⊢; exact hcwr₁1'
  have hagree1'_f : agreeOnClean predSat ctxFalse'.regime ctxFalse'
      cfg₀1.memory cfg₀1.varEnv θ₀1 cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simp only [agreeOnClean, ctxFalse', ctxFalse] at hagree1' ⊢; exact hagree1'
  -- Thread extern registry for cfg₀1.
  have hreg_cfg₀1_e3 : cfg₀1.registry = registry := by
    simpa using terminatesTo_preserves_registry ht₀_e1
  have hcfg₀1_eq_e3 : cfg₀1 = { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry } :=
    config_eq_of_registry cfg₀1 registry hreg_cfg₀1_e3
  have ht₀_e3' : terminatesTo e3 { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry } cf₀ o₀ := by
    rw [← hcfg₀1_eq_e3]; exact ht₀_e3
  have hwfcf₀1'_e3 : wfConfig { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry } := by
    rw [← hcfg₀1_eq_e3]; exact hwfcf₀1
  -- Thread RegistryReservedWF and ReservedDiscipline through e1 evaluation for e3's IH
  have hres₀1_e3 : RegistryReservedWF registry cfg₀1.memory cfg₀1.nextAddr := by
    apply RegistryReservedWF_mono hres₀
    · exact terminatesTo_memory_contains_mono e1
        { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm, registry := registry }
        cfg₀1 (Value.bool b₀) hOp ht₀_e1
    · exact terminatesTo_nextAddr_mono e1
        { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm, registry := registry }
        cfg₀1 (Value.bool b₀) hOp ht₀_e1
  have hres₁1_e3 : RegistryReservedWF registry cfg₁1.memory cfg₁1.nextAddr := by
    apply RegistryReservedWF_mono hres₁
    · exact terminatesTo_memory_contains_mono e1
        { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm, registry := registry }
        cfg₁1 (Value.bool b₁) hOp ht₁_e1
    · exact terminatesTo_nextAddr_mono e1
        { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm, registry := registry }
        cfg₁1 (Value.bool b₁) hOp ht₁_e1
  -- Serial threading: the else-arm context carries the then-arm's declared set,
  -- and e2's (unexecuted) typechecking only grows res1.declared'.
  have hsub₂ : ∀ id, id ∈ res1.declared' → id ∈ _res2.declared' :=
    fun id h => typecheck_declared'_mono _ e2 fuel' _res2 (by simpa [typecheck] using _htc2) id h
  have hrd₀_e3 : ReservedDiscipline registry ctxFalse'.declaredExternRefs θ₀1 := by
    simp only [ctxFalse']
    exact ReservedDiscipline.mono_declared hsub₂ (by simpa [hreg_cfg₀1_e3] using _hrd₀1)
  have hrd₁_e3 : ReservedDiscipline registry ctxFalse'.declaredExternRefs θ₁1 := by
    have hreg₁1_e3 : cfg₁1.registry = registry := by simpa using terminatesTo_preserves_registry ht₁_e1
    simp only [ctxFalse']
    exact ReservedDiscipline.mono_declared hsub₂ (by simpa [hreg₁1_e3] using _hrd₁1)
  have hroot₀3 : P₀ ⟨ctxFalse', e3, fuel',
      { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry }⟩ := by
    rw [← hcfg₀1_eq_e3]
    exact hprem.run₀.closed hroot₀ (SubStep.iteElseMatched (f := fuel') hmatch hregime_false htc1
      (by simpa [hb₀_false] using ht₀_e1) _htc2)
  have hroot₁3 : P₁ ⟨ctxFalse', e3, fuel',
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry }⟩ := by
    rw [← hcfg₁1_eq]
    exact hprem.run₁.closed hroot₁ (SubStep.iteElseMatched (f := fuel') hmatch hregime_false htc1
      (by simpa [hb₁_false] using ht₁_e1) _htc2)
  have hstep_e3 :=
    hIH_e3 hpredlaws hframe'.right hwfTm_false hTmBounded_false hfp_false
      cfg₀1.memory cfg₁1.memory cfg₀1.varEnv cfg₁1.varEnv θ₀1 θ₁1
      cf₀ cf₁ o₀ o₁
      hθ₀1wf hθ₁1wf hwf_false' htagBounded_false hric₀1'_f hric₁1'_f htagR_false'
      hcwr₀1'_f hcwr₁1'_f hagree1'_f
      cfg₀1.nextAddr cfg₁1.nextAddr cfg₀1.pureMode hwfcf₀1'_e3 hwfcf₁1'
      hres₀1_e3 hres₁1_e3 hrd₀_e3 hrd₁_e3 ht₀_e3' ht₁_e3' hprem hroot₀3 hroot₁3
  rcases hstep_e3 with ⟨tm3, hcanon3, hpredlaws3, hresTm3, hstep_e3⟩
  rcases hstep_e3 with
    ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, _hvtyp₀3, _hvtyp₁3, _hTm3, hwf3, _htagBounded3, hwfcf₀3, hwfcf₁3,
      hric₀3, hric₁3, htagR3, hcwr₀3, hcwr₁3, hagree3, _hvalc₀3, _hvalc₁3, hres_agree3, _hrd₀3, _hrd₁3, hM₀3, hM₁3, hF₀3, hF₁3⟩
  have hθext₀ : wfExtendsMap θ₀ θ₀2 := wfExtendsMap_trans hθext₀1 hθext₀2
  have hθext₁ : wfExtendsMap θ₁ θ₁2 := wfExtendsMap_trans hθext₁1 hθext₁2
  -- Field-level reasoning: ctxAfter ctxᵢ res and ctxAfter ctxFalse' res3 agree on relevant fields
  have hctxAfter_memEnv : (ctxAfter ctxᵢ res).memEnv = (ctxAfter ctxFalse' res3).memEnv := by
    simp [ctxAfter, hmemEnv]
  have hctxAfter_tagEnv : (ctxAfter ctxᵢ res).tagEnv = (ctxAfter ctxFalse' res3).tagEnv := by
    simp [ctxAfter, htagEnv]
  have hctxAfter_varEnv : (ctxAfter ctxᵢ res).varEnv = (ctxAfter ctxFalse' res3).varEnv := by
    simp [ctxAfter, ctxFalse', ctxFalse]
  have hctxAfter_regime : (ctxAfter ctxᵢ res).regime = (ctxAfter ctxFalse' res3).regime := by
    simp [ctxAfter, hregime']
  -- Footprint bookkeeping: compose the condition run and the else-branch run.
  have hRback : ∀ k' d, tm.lookup k' = some d → (ctxAfter ctxFalse' res3).regime.lookup? k' ≠ none →
      (ctxAfter { ctxᵢ with pureCtx := true } res1).regime.lookup? k' ≠ none := by
    intro k' d hd hk'
    have h := regime_defined_back (regime_monotoneExt ctxFalse' e3 fuel' res3 htc3')
      hTmBounded_false k' d hd (by simpa [ctxAfter] using hk')
    rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
    cases hl : ctxFalse'.regime.lookup? k' with
    | none => exact absurd hl h
    | some b =>
        have hb := typecheckExpr_pure_regime_bridge_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1 k' b (by simpa [ctxFalse', ctxFalse] using hl)
        simp [ctxAfter, hb]
  have hM₀_case : MapKeepsBelow ctxᵢ.nextLoc θ₀ θ₀2 := hM₀1.trans hM₀3 hle_nl
  have hM₁_case : MapKeepsBelow ctxᵢ.nextLoc θ₁ θ₁2 := hM₁1.trans hM₁3 hle_nl
  have hF₀_case : KeepsFootprints tm (ctxAfter ctxᵢ res).regime θ₀ μ₀ cf₀.memory := by
    rw [hctxAfter_regime]
    exact KeepsFootprints.trans hF₀1 hF₀3 (TagMeaningExtends.refl tm) hθext₀1.1 hRback
  have hF₁_case : KeepsFootprints tm (ctxAfter ctxᵢ res).regime θ₁ μ₁ cf₁.memory := by
    rw [hctxAfter_regime]
    exact KeepsFootprints.trans hF₁1 hF₁3 (TagMeaningExtends.refl tm) hθext₁1.1 hRback
  have hric₀_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
    simp only [runtimeInstantiatesCtx, hctxAfter_memEnv, hctxAfter_varEnv]
    exact hric₀3
  have hric₁_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
    simp only [runtimeInstantiatesCtx, hctxAfter_memEnv, hctxAfter_varEnv]
    exact hric₁3
  have htag_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) := by
    simp only [regimeConsistentWithCtx, ctxAfter, htagEnv, hregime']
    exact htagR3
  have hcwr₀_final :
      consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf₀.memory cf₀.varEnv θ₀2 := by
    simp only [consistentWithRegime, hctxAfter_regime, hctxAfter_memEnv, hctxAfter_varEnv]
    exact hcwr₀3
  have hcwr₁_final :
      consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf₁.memory cf₁.varEnv θ₁2 := by
    simp only [consistentWithRegime, hctxAfter_regime, hctxAfter_memEnv, hctxAfter_varEnv]
    exact hcwr₁3
  have hagree_final :
      agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁2 := by
    simp only [agreeOnClean, hctxAfter_regime, hctxAfter_memEnv, hctxAfter_varEnv]
    exact hagree3
  have hresTm : QTypRespectsTagMeaning tm3 res.qualType := by
    have hguard : qtypGuardDesc? res.qualType = none := by
      simp [qtypGuardDesc?, hpredNo]
    intro qt' k' d hinq hqd
    exact
      (QTypRespectsTagMeaning_transport_etyp_noGuard
        tm3 res3.qualType res.qualType hresTm3 hetyp hguard) hinq hqd
  have hTm_final : wfTagMeaningCtx tm3 (ctxAfter ctxᵢ res) := by
    simp only [wfTagMeaningCtx] at _hTm3 ⊢
    rwa [hctxAfter_varEnv, hctxAfter_memEnv]
  have hboundary_ite : BoundaryTagMeaningPost ctxᵢ res predSat tm tm3 := by
    exact ⟨hcanon3.1, by rw [_hnextTag]; exact hcanon3.2.1.mono (Nat.le_max_right _ _),
      hTm_final, hresTm, hpredlaws3,
      hcanon3.within.mono_log (fun a ha => by rw [hlog]; simp [ha])⟩
  refine ⟨tm3, hboundary_ite, hpredlaws3, hresTm, ?_⟩
  refine ⟨θ₀2, θ₁2, hθext₀, hθext₁, ?_, ?_, ?_, ?_, ?_, hwfcf₀3, hwfcf₁3,
    hric₀_final, hric₁_final, htag_final, hcwr₀_final, hcwr₁_final, hagree_final,
    ?_, ?_, ?_, ?_, ?_, hM₀_case, hM₁_case, hF₀_case, hF₁_case⟩
  · simpa [hetyp] using _hvtyp₀3
  · simpa [hetyp] using _hvtyp₁3
  · exact hTm_final
  · -- wfTypeContext: depends on memEnv and nextLoc (monotone in nextLoc)
    simp only [wfTypeContext, ctxAfter, hnextLoc]
    refine ⟨?_, varEnvRefLocsBounded_mono hwf3.2.1 (by simp [ctxAfter]),
             varEnvClosuresCapturedRefLocsBounded_mono hwf3.2.2 (by simp [ctxAfter])⟩
    intro l hl
    rw [hmemEnv] at hl
    exact Nat.lt_of_lt_of_le (hwf3.1 l (by simpa [ctxAfter] using hl)) (Nat.le_max_right _ _)
  · -- TagBoundedCtx (ctxAfter ctxᵢ res)
    exact typecheckExpr_preserves_TagBoundedCtx ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res (by simpa [typecheck] using htc) htagBounded
  · refine valueConsistentWithRegime.noTag (predSat := predSat) (R := (ctxAfter ctxᵢ res).regime)
      (qt := res.qualType) (μ := cf₀.memory) (v := o₀) ?_ ?_
    · simp [qtypGuardTag, hpredNo]
    · have hcap₃ : closureCapturedVarsRegime predSat (ctxAfter ctxFalse' res3).regime res3.qualType cf₀.memory θ₀2 o₀ :=
        valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₀3
      have hcap₃' : closureCapturedVarsRegime predSat (ctxAfter ctxᵢ res).regime res3.qualType cf₀.memory θ₀2 o₀ := by
        rwa [hctxAfter_regime]
      exact closureCapturedVarsRegime_transport_etyp hetyp.symm hcap₃'
  · refine valueConsistentWithRegime.noTag (predSat := predSat) (R := (ctxAfter ctxᵢ res).regime)
      (qt := res.qualType) (μ := cf₁.memory) (v := o₁) ?_ ?_
    · simp [qtypGuardTag, hpredNo]
    · have hcap₃ : closureCapturedVarsRegime predSat (ctxAfter ctxFalse' res3).regime res3.qualType cf₁.memory θ₁2 o₁ :=
        valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₁3
      have hcap₃' : closureCapturedVarsRegime predSat (ctxAfter ctxᵢ res).regime res3.qualType cf₁.memory θ₁2 o₁ := by
        rwa [hctxAfter_regime]
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
      rw [hctxAfter_regime]; exact hres_agree3
    have hagree3' :
        agreeValueUnder predSat (ctxAfter ctxᵢ res).regime
          cf₀.memory cf₁.memory θ₀2 θ₁2 res3.qualType o₀ o₁ :=
      hres_agree3' hclean3
    exact agreeValueUnder_transport_clean hclean hetyp hpoison_imp hagree3'
  · -- ReservedDiscipline for θ₀2: res.declared' is exactly the executed arm's set
    rw [hdecl']
    exact _hrd₀3
  · -- ReservedDiscipline for θ₁2: same
    rw [hdecl']
    exact _hrd₁3

lemma typecheckIf_standard_compat_from_existing_hyps
    (ctxᵢ : TypeContext) (e1 e2 e3 : Expr) (fuel' : Nat)
    (res res1 res2 res3 : TypeResult)
    (hstdCase :
      ((∃ (k : Tag) (deps : Deps),
          matchGuard e1 ctxᵢ.memEnv ctxᵢ.varEnv fuel' = .ok (k, deps) ∧
          ctxᵢ.regime.lookup? k = none)
        ∨
        (∃ err, matchGuard e1 ctxᵢ.memEnv ctxᵢ.varEnv fuel' = .error err)))
    (htc1 : typecheckExpr ctxᵢ e1 fuel' = .ok res1)
    (hbool : res1.qualType.etyp = ETyp.bool)
    (htc2 : (let ctx' := { ctxᵢ with memEnv := res1.memEnv', tagEnv := res1.tagEnv', nextLoc := res1.nextLoc', nextTag := res1.nextTag', regime := res1.regime', declaredExternRefs := res1.declared' }
             let pc' := joinPoison ctxᵢ.pc res1.qualType.poison
             let ctx'' := { ctx' with pc := pc' }
             typecheckExpr ctx'' e2 fuel' = .ok res2))
    (htc3 : (let ctx' := { ctxᵢ with memEnv := res1.memEnv', tagEnv := res1.tagEnv', nextLoc := res1.nextLoc', nextTag := res1.nextTag', regime := res1.regime', declaredExternRefs := res1.declared' }
             let pc' := joinPoison ctxᵢ.pc res1.qualType.poison
             let ctx'' := { ctx' with pc := pc' }
             let ctxForE3 := { ctx'' with nextLoc := res2.nextLoc', nextTag := res2.nextTag',
                                          declaredExternRefs := res2.declared' }
             typecheckExpr ctxForE3 e3 fuel' = .ok res3))
    (htcIf : typecheckIf ctxᵢ e1 e2 e3 (Nat.succ fuel') = .ok res) :
    beqETypSignature res2.qualType.etyp res3.qualType.etyp = true := by
  by_contra hcompat_ne
  have hcompat_false : beqETypSignature res2.qualType.etyp res3.qualType.etyp = false := by
    cases hbeq : beqETypSignature res2.qualType.etyp res3.qualType.etyp <;> simp_all
  cases hstdCase with
  | inl hmatch_none =>
      obtain ⟨k, deps, hmatch, hregime_none⟩ := hmatch_none
      unfold typecheckIf at htcIf
      simp only [bind, Except.bind, hmatch, hregime_none] at htcIf
      cases htc1pure : typecheckExpr { ctxᵢ with pureCtx := true } e1 fuel' with
      | error _ =>
          simp [htc1pure] at htcIf
      | ok guardResult =>
          simp [htc1pure] at htcIf
          cases hqGuard : guardResult.qualType with
          | mk guardEtyp guardP guardPred =>
              simp only [hqGuard] at htcIf
              by_cases hguardBool : guardEtyp = ETyp.bool
              · simp [hguardBool, pure, Except.pure] at htcIf
                cases htc1' : typecheckExpr ctxᵢ e1 fuel' with
                | error _ =>
                    simp [htc1'] at htcIf
                | ok result1 =>
                    simp [htc1'] at htcIf
                    have hres1 : result1 = res1 := by
                      rw [htc1] at htc1'
                      injection htc1' with hEq
                      exact hEq.symm
                    subst result1
                    cases hq1 : res1.qualType with
                    | mk etyp1 p1 pred1 =>
                        have hbool' : etyp1 = ETyp.bool := by
                          simpa [hq1] using hbool
                        simp [hq1, hbool'] at htcIf
                        let ctx2 : TypeContext :=
                          { ctxᵢ with
                            memEnv := res1.memEnv'
                            tagEnv := res1.tagEnv'
                            nextLoc := res1.nextLoc'
                            nextTag := res1.nextTag'
                            regime := res1.regime'
                            pc := joinPoison ctxᵢ.pc p1
                            declaredExternRefs := res1.declared' }
                        cases htc2' : typecheckExpr ctx2 e2 fuel' with
                        | error _ =>
                            simp [ctx2, htc2'] at htcIf
                        | ok result2 =>
                            simp [ctx2, htc2'] at htcIf
                            have hres2 : result2 = res2 := by
                              have htc2'' : typecheckExpr ctx2 e2 fuel' = .ok res2 := by
                                simpa [ctx2, hq1] using htc2
                              rw [htc2''] at htc2'
                              injection htc2' with hEq
                              exact hEq.symm
                            subst result2
                            cases hq2 : res2.qualType with
                            | mk etyp2 p2 pred2 =>
                                let ctxForE3 : TypeContext :=
                                  { ctx2 with nextLoc := res2.nextLoc', nextTag := res2.nextTag', declaredExternRefs := res2.declared' }
                                cases htc3' : typecheckExpr ctxForE3 e3 fuel' with
                                | error _ =>
                                    exfalso
                                    have htcIf' := htcIf
                                    simp [ctx2, ctxForE3, hq2, htc3'] at htcIf'
                                | ok result3 =>
                                    have htcIf' := htcIf
                                    simp [ctx2, ctxForE3, htc3'] at htcIf'
                                    have hres3 : result3 = res3 := by
                                      have htc3'' : typecheckExpr ctxForE3 e3 fuel' = .ok res3 := by
                                        simpa [ctxForE3, ctx2, hq1, hq2] using htc3
                                      rw [htc3''] at htc3'
                                      injection htc3' with hEq
                                      exact hEq.symm
                                    subst result3
                                    cases hq3 : res3.qualType with
                                    | mk etyp3 p3 pred3 =>
                                        simp [hq2, hq3] at hcompat_false
                                        simp [hq2, hq3, hcompat_false] at htcIf'
              · simp [hguardBool] at htcIf
  | inr hmatch_fail =>
      obtain ⟨err, hmatch_fail⟩ := hmatch_fail
      unfold typecheckIf at htcIf
      simp only [bind, Except.bind, hmatch_fail] at htcIf
      cases htc1' : typecheckExpr ctxᵢ e1 fuel' with
      | error _ =>
          simp [htc1'] at htcIf
      | ok result1 =>
          simp [htc1'] at htcIf
          have hres1 : result1 = res1 := by
            rw [htc1] at htc1'
            injection htc1' with hEq
            exact hEq.symm
          subst result1
          cases hq1 : res1.qualType with
          | mk etyp1 p1 pred1 =>
              have hbool' : etyp1 = ETyp.bool := by
                simpa [hq1] using hbool
              simp [hq1, hbool'] at htcIf
              let ctx2 : TypeContext :=
                { ctxᵢ with
                  memEnv := res1.memEnv'
                  tagEnv := res1.tagEnv'
                  nextLoc := res1.nextLoc'
                  nextTag := res1.nextTag'
                  regime := res1.regime'
                  pc := joinPoison ctxᵢ.pc p1
                  declaredExternRefs := res1.declared' }
              cases htc2' : typecheckExpr ctx2 e2 fuel' with
              | error _ =>
                  simp [ctx2, htc2'] at htcIf
              | ok result2 =>
                  simp [ctx2, htc2'] at htcIf
                  have hres2 : result2 = res2 := by
                    have htc2'' : typecheckExpr ctx2 e2 fuel' = .ok res2 := by
                      simpa [ctx2, hq1] using htc2
                    rw [htc2''] at htc2'
                    injection htc2' with hEq
                    exact hEq.symm
                  subst result2
                  cases hq2 : res2.qualType with
                  | mk etyp2 p2 pred2 =>
                      let ctxForE3 : TypeContext :=
                        { ctx2 with nextLoc := res2.nextLoc', nextTag := res2.nextTag', declaredExternRefs := res2.declared' }
                      cases htc3' : typecheckExpr ctxForE3 e3 fuel' with
                      | error _ =>
                          exfalso
                          have htcIf' := htcIf
                          simp [ctx2, ctxForE3, hq2, htc3'] at htcIf'
                      | ok result3 =>
                          have htcIf' := htcIf
                          simp [ctx2, ctxForE3, htc3'] at htcIf'
                          have hres3 : result3 = res3 := by
                            have htc3'' : typecheckExpr ctxForE3 e3 fuel' = .ok res3 := by
                              simpa [ctxForE3, ctx2, hq1, hq2] using htc3
                            rw [htc3''] at htc3'
                            injection htc3' with hEq
                            exact hEq.symm
                          subst result3
                          cases hq3 : res3.qualType with
                          | mk etyp3 p3 pred3 =>
                              simp [hq2, hq3] at hcompat_false
                              simp [hq2, hq3, pure, Except.pure, hcompat_false] at htcIf'

-- Standard conservative if case: either matchGuard fails or the matched regime is absent.
private lemma stepFR_ite_standard
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 e3 : Expr) (fuel' : Nat) (res : TypeResult)
  (CanUse : Expr → Prop) (CtxReach : TypeContext → Prop)
  (hOp : RegistryOperationalSafe registry)
  (hctxCurrent : CtxReach ctxᵢ)
  (hcan1 : CanUse e1) (hcan2 : CanUse e2) (hcan3 : CanUse e3)
  (IH :
    StepFR_IH_WithExprCtx predSat tm (Nat.succ (Nat.succ fuel'))
      CanUse CtxReach (registry := registry))
  (singleIH :
    StepFRSingleRunFinalCleanPcTrue_IH_WithExprCtx
      predSat tm (Nat.succ (Nat.succ fuel')) CanUse CtxReach (registry := registry))
  (hkeepFP : TypingKeepsFootprintCtx)
  (htc : typecheck ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) = .ok res)
  (res1 res2 res3 : TypeResult)
  (htc1 : typecheckExpr ctxᵢ e1 fuel' = .ok res1)
  (hbool : res1.qualType.etyp = ETyp.bool)
  (htc2 : (let ctx' := { ctxᵢ with memEnv := res1.memEnv', tagEnv := res1.tagEnv', nextLoc := res1.nextLoc', nextTag := res1.nextTag', regime := res1.regime', declaredExternRefs := res1.declared' }
           let pc' := joinPoison ctxᵢ.pc res1.qualType.poison
           let ctx'' := { ctx' with pc := pc' }
           typecheckExpr ctx'' e2 fuel' = .ok res2))
  (htc3 : (let ctx' := { ctxᵢ with memEnv := res1.memEnv', tagEnv := res1.tagEnv', nextLoc := res1.nextLoc', nextTag := res1.nextTag', regime := res1.regime', declaredExternRefs := res1.declared' }
           let pc' := joinPoison ctxᵢ.pc res1.qualType.poison
           let ctx'' := { ctx' with pc := pc' }
           let ctxForE3 := { ctx'' with nextLoc := res2.nextLoc', nextTag := res2.nextTag',
                                        declaredExternRefs := res2.declared' }
           typecheckExpr ctxForE3 e3 fuel' = .ok res3))
  (hctxThen :
    CtxReach
      { { ctxᵢ with
          memEnv := res1.memEnv',
          tagEnv := res1.tagEnv',
          nextLoc := res1.nextLoc',
          nextTag := res1.nextTag',
          regime := res1.regime',
          declaredExternRefs := res1.declared' } with
        pc := joinPoison ctxᵢ.pc res1.qualType.poison })
  (hctxElse :
    CtxReach
      { { { ctxᵢ with
            memEnv := res1.memEnv',
            tagEnv := res1.tagEnv',
            nextLoc := res1.nextLoc',
            nextTag := res1.nextTag',
            regime := res1.regime',
            declaredExternRefs := res1.declared' } with
          pc := joinPoison ctxᵢ.pc res1.qualType.poison } with
        nextLoc := res2.nextLoc',
        nextTag := res2.nextTag',
        declaredExternRefs := res2.declared' })
  (hmemEnv : res.memEnv' = joinMemEnvsStrong res2.memEnv' res3.memEnv')
  (htagEnv : res.tagEnv' = joinTagEnvs res2.tagEnv' res3.tagEnv')
  (hnextLoc : res.nextLoc' = max res2.nextLoc' res3.nextLoc')
  (hnextTag : res.nextTag' = max res2.nextTag' res3.nextTag')
  (hregime' : res.regime' = joinRegimes res2.regime' res3.regime')
  (hdecl' : res.declared' = res3.declared')
  (hpoison : res.qualType.poison = joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison
                          (joinPoison res2.qualType.poison res3.qualType.poison)))
  (hcompat : beqETypSignature res2.qualType.etyp res3.qualType.etyp = true)
  (hetyp : res.qualType.etyp =
            joinETyps res2.qualType.etyp res3.qualType.etyp
              res2.qualType.poison res3.qualType.poison)
  (hpredNo : res.qualType.pred = Predicate.noPred)
  (hlog : res.tagLog' = res1.tagLog' ++ res2.tagLog' ++ res3.tagLog')
  (hstd : StdArm ctxᵢ e1 fuel') :
  StepFR ctxᵢ (Expr.ite e1 e2 e3) res predSat tm (Nat.succ (Nat.succ fuel')) (registry := registry) := by
  classical
  intro hpredlaws hframe hwfTm hTmBounded hfp μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁
    hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm
    hwfcfg₀ hwfcfg₁ hres₀ hres₁ hrd₀ hrd₁ ht₀ ht₁ P₀ P₁ hprem hroot₀ hroot₁
  have hframe' := hframe.of_log_eq hlog
  -- Invert ite evaluation
  have hstruct₀ := terminatesTo_ite_inv' e1 e2 e3
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm, registry := registry } cf₀ o₀ ht₀
  rcases hstruct₀ with ⟨cfg₀1, b₀, ht₀_e1, hbranch₀, hpm₀1, hpm₀_final⟩
  have hstruct₁ := terminatesTo_ite_inv' e1 e2 e3
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm, registry := registry } cf₁ o₁ ht₁
  rcases hstruct₁ with ⟨cfg₁1, b₁, ht₁_e1, hbranch₁, hpm₁1, hpm₁_final⟩
  -- Apply IH to e1 (without pureCtx in this mode)
  have htc1' : typecheck ctxᵢ e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have hIH_e1 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 ctxᵢ hctxCurrent hcan1 hwfTm htagBounded res1 htc1'
  have hstep_e1 :=
    hIH_e1 hpredlaws hframe'.left.left hwfTm hTmBounded hfp μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 (Value.bool b₀) (Value.bool b₁)
      hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree
      a₀ a₁ pm hwfcfg₀ hwfcfg₁ hres₀ hres₁ hrd₀ hrd₁ ht₀_e1 ht₁_e1
      hprem (hprem.run₀.closed hroot₀ (SubStep.iteCondStd (f := fuel') hstd))
      (hprem.run₁.closed hroot₁ (SubStep.iteCondStd (f := fuel') hstd))
  rcases hstep_e1 with ⟨tm1, hcanon1, hpredlaws1, hresTm1, hstep_e1⟩
  rcases hstep_e1 with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, _hvtyp₀1, _hvtyp₁1,
    hwfTm1, hwf1, htagBounded1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1,
    hcwr₀1, hcwr₁1, hagree1, hvalc₀1, hvalc₁1, hres_agree1, _hrd₀1, _hrd₁1, hM₀1, hM₁1, hF₀1, hF₁1⟩
  let ctx' := { ctxᵢ with
    memEnv := res1.memEnv'
    tagEnv := res1.tagEnv'
    nextLoc := res1.nextLoc'
    nextTag := res1.nextTag'
    regime := res1.regime'
    declaredExternRefs := res1.declared' }
  let pc' := joinPoison ctxᵢ.pc res1.qualType.poison
  let ctx'' := { ctx' with pc := pc' }
  let ctxForE3 := { ctx'' with nextLoc := res2.nextLoc', nextTag := res2.nextTag',
                               declaredExternRefs := res2.declared' }
  let resJoin : TypeResult := {
    qualType := ⟨joinETyps res2.qualType.etyp res3.qualType.etyp
        res2.qualType.poison res3.qualType.poison,
      joinPoison pc' (joinPoison res2.qualType.poison res3.qualType.poison),
      match joinETyps res2.qualType.etyp res3.qualType.etyp
          res2.qualType.poison res3.qualType.poison with
      | ETyp.arrow _ _ _ _ => Predicate.noPred
      | ETyp.parrow _ _ _ _ => Predicate.noPred
      | _ => joinPredicates res2.qualType.pred res3.qualType.pred⟩
    memEnv' := joinMemEnvsStrong res2.memEnv' res3.memEnv'
    tagEnv' := joinTagEnvs res2.tagEnv' res3.tagEnv'
    nextLoc' := max res2.nextLoc' res3.nextLoc'
    nextTag' := max res2.nextTag' res3.nextTag'
    regime' := joinRegimes res2.regime' res3.regime'
    declared' := res2.declared'
    tagLog' := res2.tagLog' ++ res3.tagLog' }
  have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀
  have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁
  have htc2' : typecheck ctx'' e2 fuel' = .ok res2 := by
    simpa [ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using htc2
  have htc3' : typecheck ctxForE3 e3 fuel' = .ok res3 := by
    simpa [ctxForE3, ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using htc3
  have hjoin :
      joinTypeResults ctx'' res2 [res3] = .ok resJoin := by
    cases hq2 : res2.qualType with
    | mk etyp2 p2 pred2 =>
        cases hq3 : res3.qualType with
        | mk etyp3 p3 pred3 =>
            have hcompat23' : beqETypSignature etyp2 etyp3 = true := by
              simpa [hq2, hq3] using hcompat
            unfold joinTypeResults
            simp [resJoin, ctx'', hq2, hq3, hcompat23', bind, Except.bind, pure, Except.pure]
            rfl
  have hresJoin_etyp : resJoin.qualType.etyp = res.qualType.etyp := by
    simpa [resJoin] using hetyp.symm
  have hresJoin_poison : resJoin.qualType.poison = res.qualType.poison := by
    simp [resJoin, pc', hpoison, joinPoison, Bool.or_assoc]
  have hmono2 : Regime.monotoneStepExt res1.regime' res2.regime' (fun k => res1.nextTag' ≤ k) := by
    simpa [ctxAfter, ctx'', ctx', pc'] using regime_monotoneExt ctx'' e2 fuel' res2 htc2'
  -- Compose with the conservative branch-join: the join keeps every `res2` entry, so the
  -- left-self-join is `monotoneStep`-monotone, and composing with `hmono2` yields the final
  -- extended-regime step `res1 → res.regime'` with fresh-tag floor `res1.nextTag'`.
  have hmono_join :
      Regime.monotoneStep res2.regime' (joinRegimes res2.regime' res3.regime') := by
    refine ⟨?_, ?_⟩
    · intro k b hk2
      cases hj : (joinRegimes res2.regime' res3.regime').lookup? k with
      | none => exact Or.inr rfl
      | some b' =>
          have hleft := joinRegimes_lookup_some_left res2.regime' res3.regime' k b' hj
          have hbb : b' = b := Option.some.inj (hleft.symm.trans hk2)
          subst hbb
          exact Or.inl rfl
    · intro k hk
      cases hj : (joinRegimes res2.regime' res3.regime').lookup? k with
      | none => exact absurd hj hk
      | some b' =>
          have hleft := joinRegimes_lookup_some_left res2.regime' res3.regime' k b' hj
          rw [hleft]; exact Option.some_ne_none b'
  have h_mono_final :
      Regime.monotoneStepExt res1.regime' res.regime' (fun k => res1.nextTag' ≤ k) := by
    rw [hregime']
    exact Regime.monotoneStepExt_trans_monotoneStep hmono2 hmono_join
  have hwf_ctx'' : wfTypeContext ctx'' := by
    simpa [ctx'', ctx', pc', ctxAfter, wfTypeContext] using hwf1
  have hwfTm_ctx'' : wfTagMeaningCtx tm1 ctx'' := by
    simpa [ctx'', ctx', pc', ctxAfter] using! hwfTm1
  have htagBounded_ctx'' : TagBoundedCtx ctx'' := by
    simpa [ctx'', ctx', pc', ctxAfter, TagBoundedCtx, tagEnvBoundedInCtx, predTagsBoundedInCtx, closureEnvBoundedInCtx] using htagBounded1
  have hTmBounded_ctx'' : TagMeaningBounded tm1 ctx''.nextTag := by
    simpa [ctx'', ctx', pc'] using BoundaryTagMeaningPost.bounded hcanon1
  have hric₀1_ctx'' : runtimeInstantiatesCtx ctx'' cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    simpa [ctx'', ctx', pc', ctxAfter, runtimeInstantiatesCtx] using hric₀1
  have hric₁1_ctx'' : runtimeInstantiatesCtx ctx'' cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [ctx'', ctx', pc', ctxAfter, runtimeInstantiatesCtx] using hric₁1
  have hcwr₀1_ctx'' :
      consistentWithRegime predSat ctx''.regime ctx''
        cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    simpa [ctx'', ctx', pc', ctxAfter, consistentWithRegime] using hcwr₀1
  have hcwr₁1_ctx'' :
      consistentWithRegime predSat ctx''.regime ctx''
        cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [ctx'', ctx', pc', ctxAfter, consistentWithRegime] using hcwr₁1
  have htagR_ctx'' : regimeConsistentWithCtx ctx'' := by
    simpa [ctx'', ctx', pc', ctxAfter, regimeConsistentWithCtx] using htagR1
  have hagree1_ctx'' :
      agreeOnClean predSat ctx''.regime ctx''
        cfg₀1.memory cfg₀1.varEnv θ₀1 cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [ctx'', ctx', pc', ctxAfter] using! hagree1
  have hnextLoc_mono :
      res1.nextLoc' ≤ res2.nextLoc' := by
    have : ctx''.nextLoc ≤ res2.nextLoc' :=
      typecheck_nextLoc_mono ctx'' e2 fuel' res2
        (by simpa [ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using htc2)
    simpa [ctx'', ctx'] using this
  have hwfTm_ctxForE3 : wfTagMeaningCtx tm1 ctxForE3 := by
    simpa [ctxForE3, ctx'', ctx', pc'] using! hwfTm1
  have htagBounded_ctxForE3 : TagBoundedCtx ctxForE3 := by
    obtain ⟨hb_tag1, ⟨hb_predV1, hb_predM1⟩, hb_clos1⟩ := htagBounded1
    have hmono : res1.nextTag' ≤ res2.nextTag' :=
      typecheck_normal_nextTag_mono ctx'' e2 fuel' res2
        (by simpa [ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using htc2)
    exact ⟨tagEnvBounded_mono res1.tagEnv' res1.nextTag' res2.nextTag' hb_tag1 hmono,
           ⟨predTagsBoundedInVarEnv_mono hb_predV1 hmono, predTagsBoundedInMemEnv_mono hb_predM1 hmono⟩,
           varEnvClosuresCapturedBounded_mono hb_clos1 hmono⟩
  have hTmBounded_ctxForE3 : TagMeaningBounded tm1 ctxForE3.nextTag := by
    have hmono : ctx''.nextTag ≤ res2.nextTag' :=
      typecheck_normal_nextTag_mono ctx'' e2 fuel' res2
        (by simpa [ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using htc2)
    simpa [ctxForE3] using hTmBounded_ctx''.mono hmono
  have hfp1 : FootprintCtx tm1 (ctxAfter ctxᵢ res1) := by
    have htc1_expr : typecheckExpr ctxᵢ e1 fuel' = .ok res1 := htc1'
    exact hkeepFP.apply htc1_expr hwfTm hTmBounded htagBounded hwf
      hcanon1.extends_tm hcanon1.within hfp
  have hfp_ctx'' : FootprintCtx tm1 ctx'' := hfp1
  have hfp_ctxForE3 : FootprintCtx tm1 ctxForE3 :=
    ⟨hfp1.1, fun k d hd l hl => Nat.lt_of_lt_of_le (hfp1.2 k d hd l hl) hnextLoc_mono⟩
  have hwf_ctxForE3 : wfTypeContext ctxForE3 := by
    simp only [wfTypeContext, ctxForE3, ctx'', ctx']
    exact ⟨fun l hl => Nat.lt_of_lt_of_le (hwf1.1 l hl) hnextLoc_mono,
           varEnvRefLocsBounded_mono hwf1.2.1 hnextLoc_mono,
           varEnvClosuresCapturedRefLocsBounded_mono hwf1.2.2 hnextLoc_mono⟩
  have hric₀1_ctxForE3 :
      runtimeInstantiatesCtx ctxForE3 cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    simpa [ctxForE3, ctx'', ctx', pc', ctxAfter, runtimeInstantiatesCtx] using hric₀1
  have hric₁1_ctxForE3 :
      runtimeInstantiatesCtx ctxForE3 cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [ctxForE3, ctx'', ctx', pc', ctxAfter, runtimeInstantiatesCtx] using hric₁1
  have hcwr₀1_ctxForE3 :
      consistentWithRegime predSat ctxForE3.regime ctxForE3
        cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    simpa [ctxForE3, ctx'', ctx', pc', ctxAfter, consistentWithRegime] using hcwr₀1
  have hcwr₁1_ctxForE3 :
      consistentWithRegime predSat ctxForE3.regime ctxForE3
        cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [ctxForE3, ctx'', ctx', pc', ctxAfter, consistentWithRegime] using hcwr₁1
  have htagR_ctxForE3 : regimeConsistentWithCtx ctxForE3 := by
    unfold regimeConsistentWithCtx at htagR1 ⊢
    simpa [ctxForE3, ctx'', ctx', pc', regimeConsistentWithCtx] using! htagR1
  -- Thread RegistryReservedWF and ReservedDiscipline through e1 evaluation
  have hres₀1 : RegistryReservedWF registry cfg₀1.memory cfg₀1.nextAddr := by
    apply RegistryReservedWF_mono hres₀
    · exact terminatesTo_memory_contains_mono e1
        { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm, registry := registry }
        cfg₀1 (Value.bool b₀) hOp ht₀_e1
    · exact terminatesTo_nextAddr_mono e1
        { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm, registry := registry }
        cfg₀1 (Value.bool b₀) hOp ht₀_e1
  have hres₁1 : RegistryReservedWF registry cfg₁1.memory cfg₁1.nextAddr := by
    apply RegistryReservedWF_mono hres₁
    · exact terminatesTo_memory_contains_mono e1
        { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm, registry := registry }
        cfg₁1 (Value.bool b₁) hOp ht₁_e1
    · exact terminatesTo_nextAddr_mono e1
        { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm, registry := registry }
        cfg₁1 (Value.bool b₁) hOp ht₁_e1
  have hreg₀1 : cfg₀1.registry = registry := by
    simpa using terminatesTo_preserves_registry ht₀_e1
  have hreg₁1 : cfg₁1.registry = registry := by
    simpa using terminatesTo_preserves_registry ht₁_e1
  have hrdStd₀ : ReservedDiscipline registry ctx''.declaredExternRefs θ₀1 := by
    simp only [ctx'', ctx']; simpa [hreg₀1] using _hrd₀1
  have hrdStd₁ : ReservedDiscipline registry ctx''.declaredExternRefs θ₁1 := by
    simp only [ctx'', ctx']; simpa [hreg₁1] using _hrd₁1
  -- Serial threading: ctxForE3 carries res2.declared'; e2's typechecking only
  -- grows the declared set, so lift the post-e1 discipline along that inclusion.
  have hsubE3 : ∀ id, id ∈ res1.declared' → id ∈ res2.declared' :=
    fun id h => typecheck_declared'_mono ctx'' e2 fuel' res2 htc2' id h
  have hsubE3' : ∀ id, id ∈ res2.declared' → id ∈ res3.declared' :=
    fun id h => typecheck_declared'_mono ctxForE3 e3 fuel' res3 htc3' id h
  have hrdStdE3₀ : ReservedDiscipline registry ctxForE3.declaredExternRefs θ₀1 := by
    simp only [ctxForE3]
    exact ReservedDiscipline.mono_declared hsubE3 (by simpa [hreg₀1] using _hrd₀1)
  have hrdStdE3₁ : ReservedDiscipline registry ctxForE3.declaredExternRefs θ₁1 := by
    simp only [ctxForE3]
    exact ReservedDiscipline.mono_declared hsubE3 (by simpa [hreg₁1] using _hrd₁1)
  -- Footprint bookkeeping shared by the four branch combinations.
  have hnl_e1 : ctxᵢ.nextLoc ≤ res1.nextLoc' := typecheck_nextLoc_mono ctxᵢ e1 fuel' res1 htc1'
  have hnt1 : ctxᵢ.nextTag ≤ res1.nextTag' := typecheck_nextTag_mono ctxᵢ e1 fuel' res1 htc1'
  have hnl_then : ctxᵢ.nextLoc ≤ ctx''.nextLoc := hnl_e1
  have hnl_else : ctxᵢ.nextLoc ≤ ctxForE3.nextLoc := Nat.le_trans hnl_e1 hnextLoc_mono
  have hRback : ∀ k d, tm.lookup k = some d → (ctxAfter ctxᵢ res).regime.lookup? k ≠ none →
      (ctxAfter ctxᵢ res1).regime.lookup? k ≠ none :=
    fun k d hd hk => regime_defined_back h_mono_final (TagMeaningBounded.mono hTmBounded hnt1) k d hd hk
  have hRleft : ∀ k d, tm1.lookup k = some d → (ctxAfter ctxᵢ res).regime.lookup? k ≠ none →
      (ctxAfter ctx'' res2).regime.lookup? k ≠ none := by
    intro k d _ hk h2
    change res.regime'.lookup? k ≠ none at hk
    change res2.regime'.lookup? k = none at h2
    rw [hregime'] at hk
    cases hj : (joinRegimes res2.regime' res3.regime').lookup? k with
    | none => exact hk hj
    | some b' =>
        have h := joinRegimes_lookup_some_left res2.regime' res3.regime' k b' hj
        rw [h2] at h
        cases h
  have hRright : ∀ k d, tm1.lookup k = some d → (ctxAfter ctxᵢ res).regime.lookup? k ≠ none →
      (ctxAfter ctxForE3 res3).regime.lookup? k ≠ none := by
    intro k d _ hk h3
    change res.regime'.lookup? k ≠ none at hk
    change res3.regime'.lookup? k = none at h3
    rw [hregime'] at hk
    cases hj : (joinRegimes res2.regime' res3.regime').lookup? k with
    | none => exact hk hj
    | some b' =>
        have h := joinRegimes_lookup_some_right res2.regime' res3.regime' k b' hj
        rw [h3] at h
        cases h
  cases hbranch₀ with
  | inl hbranch₀_true =>
      cases hbranch₁ with
      | inl hbranch₁_true =>
          have ht₀_e2 : terminatesTo e2 cfg₀1 cf₀ o₀ := hbranch₀_true.2
          have ht₁_e2 : terminatesTo e2 cfg₁1 cf₁ o₁ := hbranch₁_true.2
          have hpm_eq : cfg₁1.pureMode = cfg₀1.pureMode := by
            rw [hpm₀1, hpm₁1]
          have hcfg₁1_eq :
              cfg₁1 =
                { memory := cfg₁1.memory
                , varEnv := cfg₁1.varEnv
                , nextAddr := cfg₁1.nextAddr
                , pureMode := cfg₀1.pureMode, registry := registry } := by
            have hreg_cfg₁1_local : cfg₁1.registry = registry := by
              simpa using terminatesTo_preserves_registry ht₁_e1
            cases cfg₁1 with
            | mk m v n pm r =>
              simp only [Config.mk.injEq, true_and]
              refine ⟨hpm_eq, ?_⟩
              simpa using hreg_cfg₁1_local
          have ht₁_e2' : terminatesTo e2
              { memory := cfg₁1.memory
              , varEnv := cfg₁1.varEnv
              , nextAddr := cfg₁1.nextAddr
              , pureMode := cfg₀1.pureMode, registry := registry }
              cf₁ o₁ := by
            rw [← hcfg₁1_eq]
            exact ht₁_e2
          have hwfcf₁1' : wfConfig
              { memory := cfg₁1.memory
              , varEnv := cfg₁1.varEnv
              , nextAddr := cfg₁1.nextAddr
              , pureMode := cfg₀1.pureMode, registry := registry } := by
            rw [← hcfg₁1_eq]
            exact hwfcf₁1
          have hIH_e2 :=
            IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
              e2 ctx'' (by simpa [ctx'', ctx', pc'] using hctxThen)
                hcan2 hwfTm_ctx'' htagBounded_ctx'' res2 htc2'
          -- Thread extern registry for cfg₀1.
          have hreg_cfg₀1_m4 : cfg₀1.registry = registry := by
            simpa using terminatesTo_preserves_registry ht₀_e1
          have hcfg₀1_eq_m4 : cfg₀1 = { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry } :=
            config_eq_of_registry cfg₀1 registry hreg_cfg₀1_m4
          have ht₀_e2'' : terminatesTo e2 { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry } cf₀ o₀ := by
            rw [← hcfg₀1_eq_m4]; exact ht₀_e2
          have hwfcf₀1'_m4 : wfConfig { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry } := by
            rw [← hcfg₀1_eq_m4]; exact hwfcf₀1
          have hroot₀2 : P₀ ⟨ctx'', e2, fuel',
              { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry }⟩ := by
            rw [← hcfg₀1_eq_m4]
            exact hprem.run₀.closed hroot₀ (SubStep.iteThenStd (f := fuel') hstd htc1
              (by simpa [hbranch₀_true.1] using ht₀_e1))
          have hroot₁2 : P₁ ⟨ctx'', e2, fuel',
              { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry }⟩ := by
            rw [← hcfg₁1_eq]
            exact hprem.run₁.closed hroot₁ (SubStep.iteThenStd (f := fuel') hstd htc1
              (by simpa [hbranch₁_true.1] using ht₁_e1))
          have hstep_e2 :=
            hIH_e2 hpredlaws1 (hframe'.left.next hcanon1.within) hwfTm_ctx'' hTmBounded_ctx'' hfp_ctx''
              cfg₀1.memory cfg₁1.memory cfg₀1.varEnv cfg₁1.varEnv θ₀1 θ₁1
              cf₀ cf₁ o₀ o₁
              hθ₀1wf hθ₁1wf hwf_ctx'' htagBounded_ctx'' hric₀1_ctx'' hric₁1_ctx'' htagR_ctx''
              hcwr₀1_ctx'' hcwr₁1_ctx'' hagree1_ctx''
              cfg₀1.nextAddr cfg₁1.nextAddr cfg₀1.pureMode hwfcf₀1'_m4 hwfcf₁1'
              hres₀1 hres₁1 hrdStd₀ hrdStd₁
              ht₀_e2'' ht₁_e2' hprem hroot₀2 hroot₁2
          rcases hstep_e2 with ⟨tm2, hcanon2, hpredlaws2, hresTm2, hstep_e2⟩
          rcases hstep_e2 with
            ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, hvtyp₀2, hvtyp₁2, _hwfTm2, _hwf2, _htagBounded2, hwfcf₀2, hwfcf₁2,
              hric₀2, hric₁2, _htagR2, hcwr₀2, hcwr₁2, hagree2, hvalc₀2, hvalc₁2, hres_agree2, _hrd₀2, _hrd₁2,
              hM₀2, hM₁2, hF₀2, hF₁2⟩
          have hθext₀ : wfExtendsMap θ₀ θ₀2 := wfExtendsMap_trans hθext₀1 hθext₀2
          have hθext₁ : wfExtendsMap θ₁ θ₁2 := wfExtendsMap_trans hθext₁1 hθext₁2
          have hM₀_case : MapKeepsBelow ctxᵢ.nextLoc θ₀ θ₀2 := hM₀1.trans hM₀2 hnl_then
          have hM₁_case : MapKeepsBelow ctxᵢ.nextLoc θ₁ θ₁2 := hM₁1.trans hM₁2 hnl_then
          have hF₀_case : KeepsFootprints tm (ctxAfter ctxᵢ res).regime θ₀ μ₀ cf₀.memory :=
            KeepsFootprints.trans hF₀1 (KeepsFootprints.mono_regime hF₀2 hRleft)
              hcanon1.extends_tm hθext₀1.1 hRback
          have hF₁_case : KeepsFootprints tm (ctxAfter ctxᵢ res).regime θ₁ μ₁ cf₁.memory :=
            KeepsFootprints.trans hF₁1 (KeepsFootprints.mono_regime hF₁2 hRleft)
              hcanon1.extends_tm hθext₁1.1 hRback
          have hric₀_join :
              runtimeInstantiatesCtx (ctxAfter ctx'' resJoin) cf₀.memory cf₀.varEnv θ₀2 := by
            refine
              ite_join_transport_runtimeInstantiatesCtx
                (ctx := ctx'') (first := res2) (rest := [res3]) (res := resJoin)
                (μ := cf₀.memory) (ρ := cf₀.varEnv) (θ := θ₀2)
                hjoin ?_ hric₀2
            intro l hcontains
            rcases memEnv_lookup_some_of_contains res2.memEnv' l hcontains with ⟨qt2, hlookup2⟩
            rcases
                joinMemEnvsStrong_lookup_some_of_left_lookup
                  res2.memEnv' res3.memEnv' l qt2 hlookup2
              with ⟨qt, hlookup_join⟩
            exact memEnv_contains_of_lookup_some _ _ _ hlookup_join
          have hric₁_join :
              runtimeInstantiatesCtx (ctxAfter ctx'' resJoin) cf₁.memory cf₁.varEnv θ₁2 := by
            refine
              ite_join_transport_runtimeInstantiatesCtx
                (ctx := ctx'') (first := res2) (rest := [res3]) (res := resJoin)
                (μ := cf₁.memory) (ρ := cf₁.varEnv) (θ := θ₁2)
                hjoin ?_ hric₁2
            intro l hcontains
            rcases memEnv_lookup_some_of_contains res2.memEnv' l hcontains with ⟨qt2, hlookup2⟩
            rcases
                joinMemEnvsStrong_lookup_some_of_left_lookup
                  res2.memEnv' res3.memEnv' l qt2 hlookup2
              with ⟨qt, hlookup_join⟩
            exact memEnv_contains_of_lookup_some _ _ _ hlookup_join
          have hcwr₀_join :
              consistentWithRegime predSat
                (ctxAfter ctx'' resJoin).regime
                (ctxAfter ctx'' resJoin)
                cf₀.memory cf₀.varEnv θ₀2 := by
            exact
              consistentWithRegime_join_from_left
                predSat ctx'' res2 res3 resJoin
                cf₀.memory cf₀.varEnv θ₀2
                rfl rfl hcwr₀2
          have hcwr₁_join :
              consistentWithRegime predSat
                (ctxAfter ctx'' resJoin).regime
                (ctxAfter ctx'' resJoin)
                cf₁.memory cf₁.varEnv θ₁2 := by
            exact
              consistentWithRegime_join_from_left
                predSat ctx'' res2 res3 resJoin
                cf₁.memory cf₁.varEnv θ₁2
                rfl rfl hcwr₁2
          have h_clean_join_to_res2 :
              ∀ qt,
                qtypCleanUnder (ctxAfter ctx'' resJoin).regime qt →
                qtypCleanUnder (ctxAfter ctx'' res2).regime qt := by
            intro qt hclean
            cases hclean with
            | clean hpoison =>
                exact qtypCleanUnder.clean hpoison
            | guard k htag hk hnotfun =>
                have hk2 :
                    (ctxAfter ctx'' res2).regime.lookup? k = some true :=
                  joinTypeResults_lookup_member_regime_compat
                    (ctx := ctx'') (first := res2) (src := res2) (rest := [res3]) (res := resJoin)
                    hjoin (by simp) k true hk
                exact qtypCleanUnder.guard k htag hk2 hnotfun
          have h_mem_from_res2_or_unrealized :
              ∀ l qt,
                (ctxAfter ctx'' resJoin).memEnv.lookup l = some qt →
                qtypCleanUnder (ctxAfter ctx'' resJoin).regime qt →
                ((∃ qt2,
                    (ctxAfter ctx'' res2).memEnv.lookup l = some qt2 ∧
                    qtypCleanUnder (ctxAfter ctx'' res2).regime qt2 ∧
                    qt.etyp = qt2.etyp ∧
                    (qt.poison = false → qt2.poison = false)) ∨
                  (θ₀2.lookup l = none ∧ θ₁2.lookup l = none)) := by
            intro l qt hlookup hclean
            by_cases hlookup2_none : (ctxAfter ctx'' res2).memEnv.lookup l = none
            · right
              have hnot_contains2 : ¬ (ctxAfter ctx'' res2).memEnv.contains l := by
                intro hcontains
                have hmem : l ∈ (ctxAfter ctx'' res2).memEnv :=
                  (Std.ExtTreeMap.contains_iff_mem).1 hcontains
                have hlookup_isSome :
                    ((ctxAfter ctx'' res2).memEnv[l]?).isSome = true :=
                  (Std.ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
                have hlookup_get_none :
                    (ctxAfter ctx'' res2).memEnv[l]? = none := by
                  simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hlookup2_none
                simp [hlookup_get_none] at hlookup_isSome
              have hθ₀2_none :
                  θ₀2.lookup l = none :=
                theta_not_contains_if_not_in_memEnv
                  (ctx := (ctxAfter ctx'' res2))
                  (μ := cf₀.memory) (ρ := cf₀.varEnv) (θ := θ₀2)
                  (l := l) hric₀2 hnot_contains2
              have hθ₁2_none :
                  θ₁2.lookup l = none :=
                theta_not_contains_if_not_in_memEnv
                  (ctx := (ctxAfter ctx'' res2))
                  (μ := cf₁.memory) (ρ := cf₁.varEnv) (θ := θ₁2)
                  (l := l) hric₁2 hnot_contains2
              exact ⟨hθ₀2_none, hθ₁2_none⟩
            · left
              rcases Option.ne_none_iff_exists'.1 hlookup2_none with ⟨qt2, hlookup2⟩
              have hclean2 : qtypCleanUnder (ctxAfter ctx'' res2).regime qt2 :=
                joinTypeResults_lookup_member_clean_compat
                  (ctx := ctx'') (first := res2) (src := res2) (rest := [res3]) (res := resJoin)
                  hjoin (by simp) l qt qt2 hlookup hclean hlookup2
              have hetyp2 : qt.etyp = qt2.etyp :=
                joinTypeResults_lookup_member_etyp_compat
                  (ctx := ctx'') (first := res2) (src := res2) (rest := [res3]) (res := resJoin)
                  hjoin (by simp) l qt qt2 hlookup hlookup2
              have hpoison2 : qt.poison = false → qt2.poison = false :=
                joinTypeResults_lookup_member_poison_imp
                  (ctx := ctx'') (first := res2) (src := res2) (rest := [res3]) (res := resJoin)
                  hjoin (by simp) l qt qt2 hlookup hlookup2
              exact ⟨qt2, hlookup2, hclean2, hetyp2, hpoison2⟩
          have hlookup_back_join_to_res2 :
              ∀ k b,
                (ctxAfter ctx'' resJoin).regime.lookup? k = some b →
                (ctxAfter ctx'' res2).regime.lookup? k = some b := by
            intro k b hk
            exact
              joinTypeResults_lookup_member_regime_compat
                (ctx := ctx'') (first := res2) (src := res2) (rest := [res3]) (res := resJoin)
                hjoin (by simp) k b hk
          have hagree_join :
              agreeOnClean predSat
                (ctxAfter ctx'' resJoin).regime
                (ctxAfter ctx'' resJoin)
                cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁2 := by
            exact
              ite_join_transport_agreeOnClean_from_member
                (predSat := predSat)
                (ctx := ctx'')
                (first := res2)
                (src := res2)
                (rest := [res3])
                (res := resJoin)
                (μ₀ := cf₀.memory) (μ₁ := cf₁.memory)
                (ρ₀ := cf₀.varEnv) (ρ₁ := cf₁.varEnv)
                (θ₀ := θ₀2) (θ₁ := θ₁2)
                hjoin (by simp) hagree2
                h_clean_join_to_res2
                h_mem_from_res2_or_unrealized
                (fun {σcap} {ρcap} h =>
                  memberVarsRegimeEvidence_transport_lookup_back
                    (predSat := predSat)
                    (R := (ctxAfter ctx'' res2).regime)
                    (R' := (ctxAfter ctx'' resJoin).regime)
                    (μ := cf₀.memory)
                    hlookup_back_join_to_res2 h)
                (fun {σcap} {ρcap} h =>
                  memberCvcrEvidence_transport_lookup_back
                    (predSat := predSat)
                    (R := (ctxAfter ctx'' res2).regime)
                    (R' := (ctxAfter ctx'' resJoin).regime)
                    (μ := cf₀.memory)
                    hlookup_back_join_to_res2 h)
                (fun {σcap} {ρcap} h =>
                  memberVarsRegimeEvidence_transport_lookup_back
                    (predSat := predSat)
                    (R := (ctxAfter ctx'' res2).regime)
                    (R' := (ctxAfter ctx'' resJoin).regime)
                    (μ := cf₁.memory)
                    hlookup_back_join_to_res2 h)
                (fun {σcap} {ρcap} h =>
                  memberCvcrEvidence_transport_lookup_back
                    (predSat := predSat)
                    (R := (ctxAfter ctx'' res2).regime)
                    (R' := (ctxAfter ctx'' resJoin).regime)
                    (μ := cf₁.memory)
                    hlookup_back_join_to_res2 h)
          rcases typecheck_preserves_predSatLaws predSat tm ctxᵢ
              (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res
              hwfTm hTmBounded hframe htc with
            ⟨tmOut, hcanonOut, hpredlawsOut, hwithinOut⟩
          have hresTm : QTypRespectsTagMeaning tmOut res.qualType :=
            IsCanonicalExtension.respectsResult hcanonOut
          have hwfTm_final : wfTagMeaningCtx tmOut (ctxAfter ctxᵢ res) :=
            IsCanonicalExtension.wfCtx hcanonOut
          have hwf_final : wfTypeContext (ctxAfter ctxᵢ res) :=
            wfTypeContext_of_wfTypeResult ctxᵢ res
              (typecheckExpr_preserves_wfTypeResult
                ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res hwf htc)
              hwf (typecheck_nextLoc_mono ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res htc)
          have htagBounded_final : TagBoundedCtx (ctxAfter ctxᵢ res) :=
            typecheckExpr_preserves_TagBoundedCtx ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res (by simpa [typecheck] using htc) htagBounded
          have htag_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) :=
            typecheckExpr_preserves_regimeConsistentWithCtx
              ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res htagR htc
          have hvtyp₀_join : valueHasETyp θ₀2 o₀ resJoin.qualType.etyp := by
            exact
              joinTypeResults_transport_valueHasETyp_from_member
                (ctx := ctx'') (first := res2) (src := res2) (rest := [res3]) (res := resJoin)
                (θ := θ₀2) (v := o₀)
                hjoin (by simp) hvtyp₀2
          have hvtyp₁_join : valueHasETyp θ₁2 o₁ resJoin.qualType.etyp := by
            exact
              joinTypeResults_transport_valueHasETyp_from_member
                (ctx := ctx'') (first := res2) (src := res2) (rest := [res3]) (res := resJoin)
                (θ := θ₁2) (v := o₁)
                hjoin (by simp) hvtyp₁2
          have hvtyp₀_final : valueHasETyp θ₀2 o₀ res.qualType.etyp := by
            simpa [hresJoin_etyp] using hvtyp₀_join
          have hvtyp₁_final : valueHasETyp θ₁2 o₁ res.qualType.etyp := by
            simpa [hresJoin_etyp] using hvtyp₁_join
          have hric₀_final :
              runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using! hric₀_join
          have hric₁_final :
              runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using! hric₁_join
          have hcwr₀_final :
              consistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                (ctxAfter ctxᵢ res)
                cf₀.memory cf₀.varEnv θ₀2 := by
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using! hcwr₀_join
          have hcwr₁_final :
              consistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                (ctxAfter ctxᵢ res)
                cf₁.memory cf₁.varEnv θ₁2 := by
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using! hcwr₁_join
          have hagree_final :
              agreeOnClean predSat
                (ctxAfter ctxᵢ res).regime
                (ctxAfter ctxᵢ res)
                cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁2 := by
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using! hagree_join
          have hvalc₀_join :
              valueConsistentWithRegime predSat
                (ctxAfter ctx'' resJoin).regime
                resJoin.qualType cf₀.memory θ₀2 o₀ := by
            exact
              joinTypeResults_transport_valueConsistentWithRegime_from_member
                (predSat := predSat)
                (ctx := ctx'') (first := res2) (src := res2) (rest := [res3]) (res := resJoin)
                (μ := cf₀.memory) (θ := θ₀2) (v := o₀)
                hjoin (by simp) hvalc₀2
          have hvalc₁_join :
              valueConsistentWithRegime predSat
                (ctxAfter ctx'' resJoin).regime
                resJoin.qualType cf₁.memory θ₁2 o₁ := by
            exact
              joinTypeResults_transport_valueConsistentWithRegime_from_member
                (predSat := predSat)
                (ctx := ctx'') (first := res2) (src := res2) (rest := [res3]) (res := resJoin)
                (μ := cf₁.memory) (θ := θ₁2) (v := o₁)
                hjoin (by simp) hvalc₁2
          have hvalc₀_final :
              valueConsistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                res.qualType cf₀.memory θ₀2 o₀ := by
            refine valueConsistentWithRegime.noTag ?_ ?_
            · simp [qtypGuardTag, hpredNo]
            · have hcap_join :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    resJoin.qualType cf₀.memory θ₀2 o₀ :=
                valueConsistentWithRegime_closureCapturedVarsRegime hvalc₀_join
              have hcap_res :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    res.qualType cf₀.memory θ₀2 o₀ :=
                closureCapturedVarsRegime_transport_etyp hresJoin_etyp hcap_join
              simpa [ctxAfter, ctx'', ctx', pc', resJoin, hregime'] using hcap_res
          have hvalc₁_final :
              valueConsistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                res.qualType cf₁.memory θ₁2 o₁ := by
            refine valueConsistentWithRegime.noTag ?_ ?_
            · simp [qtypGuardTag, hpredNo]
            · have hcap_join :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    resJoin.qualType cf₁.memory θ₁2 o₁ :=
                valueConsistentWithRegime_closureCapturedVarsRegime hvalc₁_join
              have hcap_res :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    res.qualType cf₁.memory θ₁2 o₁ :=
                closureCapturedVarsRegime_transport_etyp hresJoin_etyp hcap_join
              simpa [ctxAfter, ctx'', ctx', pc', resJoin, hregime'] using hcap_res
          have hres_agree_join :
              resultAgreesIfClean predSat
                (ctxAfter ctx'' resJoin).regime
                cf₀.memory cf₁.memory θ₀2 θ₁2 resJoin.qualType o₀ o₁ := by
            exact
              joinTypeResults_transport_resultAgreesIfClean_from_member
                (predSat := predSat)
                (ctx := ctx'') (first := res2) (src := res2) (rest := [res3]) (res := resJoin)
                (μ₀ := cf₀.memory) (μ₁ := cf₁.memory)
                (θ₀ := θ₀2) (θ₁ := θ₁2)
                (o₀ := o₀) (o₁ := o₁)
                hjoin (by simp) hres_agree2
          have hres_agree_final :
              resultAgreesIfClean predSat
                (ctxAfter ctxᵢ res).regime
                cf₀.memory cf₁.memory θ₀2 θ₁2 res.qualType o₀ o₁ := by
            intro hclean
            have hclean_resJoin_reg :
                qtypCleanUnder (ctxAfter ctx'' resJoin).regime res.qualType := by
              simpa [ctxAfter, ctx'', ctx', pc', resJoin, hregime'] using hclean
            have hclean_join :
                qtypCleanUnder (ctxAfter ctx'' resJoin).regime resJoin.qualType := by
              cases hclean with
              | clean hpoison_res =>
                  exact qtypCleanUnder.clean (by simpa [hresJoin_poison] using hpoison_res)
              | guard k htag _hk _hnotfun =>
                  exfalso
                  simp [qtypGuardTag, hpredNo] at htag
            have hagree_join :
                agreeValueUnder predSat
                  (ctxAfter ctx'' resJoin).regime
                  cf₀.memory cf₁.memory θ₀2 θ₁2
                  resJoin.qualType o₀ o₁ :=
              hres_agree_join hclean_join
            have hpoison_imp :
                res.qualType.poison = false → resJoin.qualType.poison = false := by
              intro hpoison_res
              simpa [hresJoin_poison] using hpoison_res
            have hagree_res :
                agreeValueUnder predSat
                  (ctxAfter ctx'' resJoin).regime
                  cf₀.memory cf₁.memory θ₀2 θ₁2
                  res.qualType o₀ o₁ :=
              agreeValueUnder_transport_clean
                hclean_resJoin_reg hresJoin_etyp.symm hpoison_imp hagree_join
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hregime'] using hagree_res
          exact
            ⟨tmOut, BoundaryTagMeaningPost.of_isCanonical_predSat hcanonOut hpredlawsOut hwithinOut,
              hpredlawsOut, hresTm, θ₀2, θ₁2, hθext₀, hθext₁, hvtyp₀_final, hvtyp₁_final,
              hwfTm_final, hwf_final, htagBounded_final, hwfcf₀2, hwfcf₁2,
              hric₀_final, hric₁_final, htag_final,
              hcwr₀_final, hcwr₁_final, hagree_final,
              hvalc₀_final, hvalc₁_final, hres_agree_final,
              (by rw [hdecl']; exact ReservedDiscipline.mono_declared hsubE3' _hrd₀2),
              (by rw [hdecl']; exact ReservedDiscipline.mono_declared hsubE3' _hrd₁2),
              hM₀_case, hM₁_case, hF₀_case, hF₁_case⟩
      | inr hbranch₁_false =>
          have ht₀_e2 : terminatesTo e2 cfg₀1 cf₀ o₀ := hbranch₀_true.2
          have ht₁_e3 : terminatesTo e3 cfg₁1 cf₁ o₁ := hbranch₁_false.2
          have hpc_true : pc' = true := by
            cases hpc_val : pc' with
            | true =>
                rfl
            | false =>
                have hpoison1_false : res1.qualType.poison = false := by
                  have hjoin_false : joinPoison ctxᵢ.pc res1.qualType.poison = false := by
                    simpa [pc'] using hpc_val
                  exact (joinPoison_eq_false hjoin_false).2
                have hclean1 :
                    qtypCleanUnder (ctxAfter ctxᵢ res1).regime res1.qualType :=
                  qtypCleanUnder.clean hpoison1_false
                have hnotref1 : ¬ ∃ ls, res1.qualType.etyp = ETyp.ref ls := by
                  intro ⟨ls, hls⟩
                  simp [hbool] at hls
                have hnotfun1 : res1.qualType.etyp.isFunctionType = false := by
                  simp [hbool, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                have hEq_bool : Value.bool b₀ = Value.bool b₁ :=
                  agreeValueUnder_nonref_eq_of_clean
                    hclean1 hnotref1 hnotfun1 (hres_agree1 hclean1)
                cases hEq_bool
                simp [hbranch₀_true.1] at hbranch₁_false
          have hpc'' : ctx''.pc = true := by
            simpa [ctx'', pc'] using hpc_true
          have hpcForE3 : ctxForE3.pc = true := by
            simpa [ctxForE3, ctx'', pc'] using hpc_true
          have hsingle_e2 :
              StepFRSingleRunFinalCleanPcTrue ctx'' e2 res2 predSat tm1 fuel' (registry := registry) :=
            singleIH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
              e2 ctx'' (by simpa [ctx'', ctx', pc'] using hctxThen)
                hcan2 hwfTm_ctx'' hTmBounded_ctx'' res2 htc2'
          have hsingle_e3 :
              StepFRSingleRunFinalCleanPcTrue ctxForE3 e3 res3 predSat tm1 fuel' (registry := registry) :=
            singleIH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
              e3 ctxForE3 (by simpa [ctxForE3, ctx'', ctx', pc'] using hctxElse)
                hcan3 hwfTm_ctxForE3 hTmBounded_ctxForE3 res3 htc3'
          -- Thread extern registry for cfg₀1 and cfg₁1.
          have hreg_cfg₀1_s : cfg₀1.registry = registry := by
            simpa using terminatesTo_preserves_registry ht₀_e1
          have hreg_cfg₁1_s : cfg₁1.registry = registry := by
            simpa using terminatesTo_preserves_registry ht₁_e1
          have hcfg₀1_eq_s : cfg₀1 = { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry } :=
            config_eq_of_registry cfg₀1 registry hreg_cfg₀1_s
          have hcfg₁1_eq_s : cfg₁1 = { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₁1.pureMode, registry := registry } :=
            config_eq_of_registry cfg₁1 registry hreg_cfg₁1_s
          have ht₀_e2'' : terminatesTo e2 { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry } cf₀ o₀ := by
            rw [← hcfg₀1_eq_s]; exact ht₀_e2
          have ht₁_e3'' : terminatesTo e3 { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₁1.pureMode, registry := registry } cf₁ o₁ := by
            rw [← hcfg₁1_eq_s]; exact ht₁_e3
          have hwfcf₀1_s : wfConfig { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry } := by
            rw [← hcfg₀1_eq_s]; exact hwfcf₀1
          have hwfcf₁1_s : wfConfig { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₁1.pureMode, registry := registry } := by
            rw [← hcfg₁1_eq_s]; exact hwfcf₁1
          have hroot₀2s : P₀ ⟨ctx'', e2, fuel',
              { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry }⟩ := by
            rw [← hcfg₀1_eq_s]
            exact hprem.run₀.closed hroot₀ (SubStep.iteThenStd (f := fuel') hstd htc1
              (by simpa [hbranch₀_true.1] using ht₀_e1))
          have hroot₁3s : P₁ ⟨ctxForE3, e3, fuel',
              { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₁1.pureMode, registry := registry }⟩ := by
            rw [← hcfg₁1_eq_s]
            exact hprem.run₁.closed hroot₁ (SubStep.iteElseStd (f := fuel') hstd htc1
              (by simpa [hbranch₁_false.1] using ht₁_e1) htc2)
          rcases
              (hsingle_e2 hpredlaws1 (hframe'.left.next hcanon1.within) hwfTm_ctx''
                hTmBounded_ctx'' htagBounded_ctx'' hfp_ctx'').2
                cfg₀1.memory cfg₀1.varEnv θ₀1 cf₀ o₀
                hθ₀1wf hwf_ctx'' hric₀1_ctx'' htagR_ctx''
                hcwr₀1_ctx'' cfg₀1.nextAddr cfg₀1.pureMode hwfcf₀1_s hres₀1 hrdStd₀ ht₀_e2'' hpc''
                hprem.run₀ hroot₀2s
            with ⟨θ₀2, hθext₀2, hvtyp₀2, hric₀2, hcwr₀2, hvalc₀2, hpres₂, _hfresh₂, hrdS₀2, hM₀2, hF₀2⟩
          rcases
              (hsingle_e3 hpredlaws1 (hframe'.skip hcanon1.within) hwfTm_ctxForE3
                hTmBounded_ctxForE3 htagBounded_ctxForE3 hfp_ctxForE3).2
                cfg₁1.memory cfg₁1.varEnv θ₁1 cf₁ o₁
                hθ₁1wf hwf_ctxForE3 hric₁1_ctxForE3 htagR_ctxForE3
                hcwr₁1_ctxForE3 cfg₁1.nextAddr cfg₁1.pureMode hwfcf₁1_s hres₁1 hrdStdE3₁ ht₁_e3'' hpcForE3
                hprem.run₁ hroot₁3s
            with ⟨θ₁3, hθext₁3, hvtyp₁3, hric₁3, hcwr₁3, hvalc₁3, hpres₃, _hfresh₃, hrdS₁3, hM₁3, hF₁3⟩
          have hθext₀ : wfExtendsMap θ₀ θ₀2 := wfExtendsMap_trans hθext₀1 hθext₀2
          have hθext₁ : wfExtendsMap θ₁ θ₁3 := wfExtendsMap_trans hθext₁1 hθext₁3
          have hM₀_case : MapKeepsBelow ctxᵢ.nextLoc θ₀ θ₀2 := hM₀1.trans hM₀2 hnl_then
          have hM₁_case : MapKeepsBelow ctxᵢ.nextLoc θ₁ θ₁3 := hM₁1.trans hM₁3 hnl_else
          have hF₀_case : KeepsFootprints tm (ctxAfter ctxᵢ res).regime θ₀ μ₀ cf₀.memory :=
            KeepsFootprints.trans hF₀1 (KeepsFootprints.mono_regime hF₀2 hRleft)
              hcanon1.extends_tm hθext₀1.1 hRback
          have hF₁_case : KeepsFootprints tm (ctxAfter ctxᵢ res).regime θ₁ μ₁ cf₁.memory :=
            KeepsFootprints.trans hF₁1 (KeepsFootprints.mono_regime hF₁3 hRright)
              hcanon1.extends_tm hθext₁1.1 hRback
          have hric₁3_src :
              runtimeInstantiatesCtx (ctxAfter ctx'' res3) cf₁.memory cf₁.varEnv θ₁3 := by
            simpa [ctxAfter, ctxForE3, ctx'', ctx', pc'] using hric₁3
          have hcwr₁3_src :
              consistentWithRegime predSat
                (ctxAfter ctx'' res3).regime
                (ctxAfter ctx'' res3)
                cf₁.memory cf₁.varEnv θ₁3 := by
            simpa [ctxAfter, ctxForE3, ctx'', ctx', pc', consistentWithRegime] using hcwr₁3
          have hvar_cf₀ : cf₀.varEnv = cfg₀1.varEnv := by
            rcases ht₀_e2 with ⟨fuel₀w, verbose₀w, heval₀w⟩
            exact (beval_preserves_varEnv e2 fuel₀w verbose₀w cfg₀1 cf₀ o₀ heval₀w).symm
          have hvar_cf₁ : cf₁.varEnv = cfg₁1.varEnv := by
            rcases ht₁_e3 with ⟨fuel₁w, verbose₁w, heval₁w⟩
            exact (beval_preserves_varEnv e3 fuel₁w verbose₁w cfg₁1 cf₁ o₁ heval₁w).symm
          rcases typecheck_preserves_predSatLaws predSat tm ctxᵢ
              (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res
              hwfTm hTmBounded hframe htc with
            ⟨tmOut, hcanonOut, hpredlawsOut, hwithinOut⟩
          have hresTm : QTypRespectsTagMeaning tmOut res.qualType :=
            IsCanonicalExtension.respectsResult hcanonOut
          have hwfTm_final : wfTagMeaningCtx tmOut (ctxAfter ctxᵢ res) :=
            IsCanonicalExtension.wfCtx hcanonOut
          have hwf_final : wfTypeContext (ctxAfter ctxᵢ res) :=
            wfTypeContext_of_wfTypeResult ctxᵢ res
              (typecheckExpr_preserves_wfTypeResult
                ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res hwf htc)
              hwf (typecheck_nextLoc_mono ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res htc)
          have htagBounded_final : TagBoundedCtx (ctxAfter ctxᵢ res) :=
            typecheckExpr_preserves_TagBoundedCtx ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res (by simpa [typecheck] using htc) htagBounded
          have htag_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) :=
            typecheckExpr_preserves_regimeConsistentWithCtx
              ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res htagR htc
          have hvtyp₀_join : valueHasETyp θ₀2 o₀ resJoin.qualType.etyp := by
            exact
              joinTypeResults_transport_valueHasETyp_from_member
                (ctx := ctx'') (first := res2) (src := res2) (rest := [res3]) (res := resJoin)
                (θ := θ₀2) (v := o₀)
                hjoin (by simp) hvtyp₀2
          have hvtyp₁_join : valueHasETyp θ₁3 o₁ resJoin.qualType.etyp := by
            exact
              joinTypeResults_transport_valueHasETyp_from_member
                (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                (θ := θ₁3) (v := o₁)
                hjoin (by simp) hvtyp₁3
          have hvtyp₀_final : valueHasETyp θ₀2 o₀ res.qualType.etyp := by
            simpa [hresJoin_etyp] using hvtyp₀_join
          have hvtyp₁_final : valueHasETyp θ₁3 o₁ res.qualType.etyp := by
            simpa [hresJoin_etyp] using hvtyp₁_join
          have hric₀_final :
              runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
            have hric₀_join :
                runtimeInstantiatesCtx (ctxAfter ctx'' resJoin) cf₀.memory cf₀.varEnv θ₀2 := by
              refine
                ite_join_transport_runtimeInstantiatesCtx
                  (ctx := ctx'') (first := res2) (rest := [res3]) (res := resJoin)
                  (μ := cf₀.memory) (ρ := cf₀.varEnv) (θ := θ₀2)
                  hjoin ?_ hric₀2
              intro l hcontains
              rcases memEnv_lookup_some_of_contains res2.memEnv' l hcontains with ⟨qt2, hlookup2⟩
              rcases
                  joinMemEnvsStrong_lookup_some_of_left_lookup
                    res2.memEnv' res3.memEnv' l qt2 hlookup2
                with ⟨qt, hlookup_join⟩
              exact memEnv_contains_of_lookup_some _ _ _ hlookup_join
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using! hric₀_join
          have hric₁_final :
              runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁3 := by
            have hric₁_join :
                runtimeInstantiatesCtx (ctxAfter ctx'' resJoin) cf₁.memory cf₁.varEnv θ₁3 := by
              unfold runtimeInstantiatesCtx at hric₁3_src ⊢
              constructor
              · intro l a hθlookup
                rcases hric₁3_src.1 l a hθlookup with ⟨hcontains3, hmem⟩
                rcases
                    memEnv_lookup_some_of_contains
                      (ctxAfter ctx'' res3).memEnv l hcontains3
                  with ⟨qt3, hlookup3ctx⟩
                have hlookup3 : res3.memEnv'.lookup l = some qt3 := by
                  simpa [ctxAfter] using hlookup3ctx
                rcases
                    joinMemEnvsStrong_lookup_some_of_right_lookup
                      res2.memEnv' res3.memEnv' l qt3 hlookup3
                  with ⟨qt, hlookup_join⟩
                have hcontains_join :
                    (joinMemEnvsStrong res2.memEnv' res3.memEnv').contains l :=
                  memEnv_contains_of_lookup_some
                    (joinMemEnvsStrong res2.memEnv' res3.memEnv') l qt hlookup_join
                exact ⟨by simpa [ctxAfter] using hcontains_join, hmem⟩
              · intro x qt hlookup
                have hlookup' :
                    (ctxAfter ctx'' res3).varEnv.lookup x = some qt := by
                  simpa [ctxAfter, ctx'', ctx', pc'] using hlookup
                exact hric₁3_src.2 hlookup'
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using! hric₁_join
          have hcwr₀_final :
              consistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                (ctxAfter ctxᵢ res)
                cf₀.memory cf₀.varEnv θ₀2 := by
            have hcwr₀_join :
                consistentWithRegime predSat
                  (ctxAfter ctx'' resJoin).regime
                  (ctxAfter ctx'' resJoin)
                  cf₀.memory cf₀.varEnv θ₀2 := by
              exact
                consistentWithRegime_join_from_left
                  predSat ctx'' res2 res3 resJoin
                  cf₀.memory cf₀.varEnv θ₀2
                  rfl rfl hcwr₀2
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using! hcwr₀_join
          have hcwr₁_final :
              consistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                (ctxAfter ctxᵢ res)
                cf₁.memory cf₁.varEnv θ₁3 := by
            have hcwr₁_join :
                consistentWithRegime predSat
                  (ctxAfter ctx'' resJoin).regime
                  (ctxAfter ctx'' resJoin)
                  cf₁.memory cf₁.varEnv θ₁3 := by
              exact
                consistentWithRegime_join_from_right
                  predSat ctx'' res2 res3 resJoin
                  cf₁.memory cf₁.varEnv θ₁3
                  rfl rfl hcwr₁3_src
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using! hcwr₁_join
          have hagree_final :
              agreeOnClean predSat
                (ctxAfter ctxᵢ res).regime
                (ctxAfter ctxᵢ res)
                cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁3 := by
            constructor
            · intro l qt hlookup hclean
              have hlookup_res : res.memEnv'.lookup l = some qt := by
                simpa [ctxAfter] using hlookup
              have hlookup_join :
                  (joinMemEnvsStrong res2.memEnv' res3.memEnv').lookup l = some qt := by
                simpa [hmemEnv] using hlookup_res
              -- Case split: l inherited from res1 vs. fresh
              by_cases hcontains_mid : res1.memEnv'.contains l
              · -- INHERITED: l ∈ res1.memEnv'
                rcases memEnv_lookup_some_of_contains res1.memEnv' l hcontains_mid with
                  ⟨qt_mid, hlookup_mid⟩
                have hclean_mid : qtypCleanUnder res1.regime' qt_mid := by
                  -- Trace clean back through e2 (which has ctx''.memEnv = res1.memEnv')
                  have hcontains_ctx'' : ctx''.memEnv.contains l := by
                    simpa [ctx'', ctx'] using hcontains_mid
                  have hcontains2 : res2.memEnv'.contains l :=
                    typecheckExpr_mem_contains_preserved
                      ctx'' e2 fuel' res2
                      (by simpa [ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using htc2)
                      l hcontains_ctx''
                  -- l is in the join, so it's in at least one branch result
                  -- Use e2 branch (which has the contains precondition satisfied)
                  rcases memEnv_lookup_some_of_contains res2.memEnv' l hcontains2 with
                    ⟨qt2, hlookup2⟩
                  have hclean2 : qtypCleanUnder res2.regime' qt2 := by
                    cases hclean with
                    | clean hpoison_out =>
                        have henv2 : res2.memEnv'.lookup l ≠ none := by
                          intro hnone; rw [hlookup2] at hnone; contradiction
                        rcases
                            joinMemEnvsStrong_lookup_clean_left
                              res2.memEnv' res3.memEnv' l qt
                              hlookup_join hpoison_out henv2
                          with ⟨qt2', hlookup2', _hetyp2, hpoison2⟩
                        have hqt2 : qt2 = qt2' := by
                          rw [hlookup2] at hlookup2'; injection hlookup2'
                        cases hqt2
                        exact qtypCleanUnder.clean hpoison2
                    | guard k htag hk hnotfun =>
                        have hk_join :
                            (joinRegimes res2.regime' res3.regime').lookup? k = some true := by
                          simpa [ctxAfter, hregime'] using hk
                        have htag2 : qtypGuardTag qt2 = some k :=
                          joinMemEnvsStrong_lookup_guardTag_left
                            res2.memEnv' res3.memEnv' l qt qt2 k
                            hlookup_join hlookup2 htag
                        have hk2 : res2.regime'.lookup? k = some true :=
                          joinRegimes_lookup_some_left
                            res2.regime' res3.regime' k true hk_join
                        have hnotfun2 : qt2.etyp.isFunctionType = false := by
                          rw [memEnv_lookup_etyp_int res2.memEnv' l qt2 hlookup2]
                          decide
                        exact qtypCleanUnder.guard k htag2 hk2 hnotfun2
                  rcases
                      typecheckExpr_clean_lookup_origin_of_pc_true
                        ctx'' e2 fuel' res2 htc2' hwf_ctx'' htagBounded_ctx'' hpc''
                        l qt2 hlookup2 hcontains_ctx'' hclean2
                    with ⟨qt_in, hlookup_in, hclean_in⟩
                  have heq_qt : qt_mid = qt_in := by
                    have : ctx''.memEnv.lookup l = some qt_mid := by
                      simpa [ctx'', ctx'] using hlookup_mid
                    rw [this] at hlookup_in; injection hlookup_in
                  subst heq_qt
                  exact hclean_in
                have hcontains2 : res2.memEnv'.contains l :=
                  typecheckExpr_mem_contains_preserved
                    ctx'' e2 fuel' res2
                    (by simpa [ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using htc2)
                    l
                    (by simpa [ctx'', ctx'] using hcontains_mid)
                have hcontains3 : res3.memEnv'.contains l :=
                  typecheckExpr_mem_contains_preserved
                    ctxForE3 e3 fuel' res3
                    (by simpa [ctxForE3, ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using htc3)
                    l
                    (by simpa [ctxForE3, ctx'', ctx'] using hcontains_mid)
                rcases memEnv_lookup_some_of_contains res2.memEnv' l hcontains2 with ⟨qt2, hlookup2⟩
                rcases memEnv_lookup_some_of_contains res3.memEnv' l hcontains3 with ⟨qt3, hlookup3⟩
                have hclean2 : qtypCleanUnder res2.regime' qt2 := by
                  cases hclean with
                  | clean hpoison_out =>
                      have henv2 : res2.memEnv'.lookup l ≠ none := by
                        intro hnone; rw [hlookup2] at hnone; contradiction
                      rcases
                          joinMemEnvsStrong_lookup_clean_left
                            res2.memEnv' res3.memEnv' l qt
                            hlookup_join hpoison_out henv2
                        with ⟨qt2', hlookup2', _hetyp2, hpoison2⟩
                      have hqt2 : qt2 = qt2' := by
                        rw [hlookup2] at hlookup2'; injection hlookup2'
                      cases hqt2
                      exact qtypCleanUnder.clean hpoison2
                  | guard k htag hk hnotfun =>
                      have hk_join :
                          (joinRegimes res2.regime' res3.regime').lookup? k = some true := by
                        simpa [ctxAfter, hregime'] using hk
                      have htag2 : qtypGuardTag qt2 = some k :=
                        joinMemEnvsStrong_lookup_guardTag_left
                          res2.memEnv' res3.memEnv' l qt qt2 k
                          hlookup_join hlookup2 htag
                      have hk2 : res2.regime'.lookup? k = some true :=
                        joinRegimes_lookup_some_left
                          res2.regime' res3.regime' k true hk_join
                      have hnotfun2 : qt2.etyp.isFunctionType = false := by
                        rw [memEnv_lookup_etyp_int res2.memEnv' l qt2 hlookup2]
                        decide
                      exact qtypCleanUnder.guard k htag2 hk2 hnotfun2
                have hclean3 : qtypCleanUnder res3.regime' qt3 := by
                  cases hclean with
                  | clean hpoison_out =>
                      have henv3 : res3.memEnv'.lookup l ≠ none := by
                        intro hnone; rw [hlookup3] at hnone; contradiction
                      rcases
                          joinMemEnvsStrong_lookup_clean_right
                            res2.memEnv' res3.memEnv' l qt
                            hlookup_join hpoison_out henv3
                        with ⟨qt3', hlookup3', _hetyp3, hpoison3⟩
                      have hqt3 : qt3 = qt3' := by
                        rw [hlookup3] at hlookup3'; injection hlookup3'
                      cases hqt3
                      exact qtypCleanUnder.clean hpoison3
                  | guard k htag hk hnotfun =>
                      have hk_join :
                          (joinRegimes res2.regime' res3.regime').lookup? k = some true := by
                        simpa [ctxAfter, hregime'] using hk
                      have htag3 : qtypGuardTag qt3 = some k :=
                        joinMemEnvsStrong_lookup_guardTag_right
                          res2.memEnv' res3.memEnv' l qt qt3 k
                          hlookup_join hlookup3 htag
                      have hk3 : res3.regime'.lookup? k = some true :=
                        joinRegimes_lookup_some_right
                          res2.regime' res3.regime' k true hk_join
                      have hnotfun3 : qt3.etyp.isFunctionType = false := by
                        rw [memEnv_lookup_etyp_int res3.memEnv' l qt3 hlookup3]
                        decide
                      exact qtypCleanUnder.guard k htag3 hk3 hnotfun3
                have hlookup_mid_ctx'' : ctx''.memEnv.lookup l = some qt_mid := by
                  simpa [ctx'', ctx'] using hlookup_mid
                have hlookup_mid_ctxForE3 : ctxForE3.memEnv.lookup l = some qt_mid := by
                  simpa [ctxForE3, ctx'', ctx'] using hlookup_mid
                have hpres_l₀ :
                    PreservesInheritedCleanLocOneRun cfg₀1.memory cf₀.memory θ₀1 θ₀2 l :=
                  PreservesInheritedFinalCleanLocsOneRun.apply
                    (ctx := ctx'') (res := res2)
                    (μ_in := cfg₀1.memory) (μ_out := cf₀.memory)
                    (θ_in := θ₀1) (θ_out := θ₀2)
                    hpres₂ hlookup_mid_ctx'' hlookup2 hclean2
                have hpres_l₁ :
                    PreservesInheritedCleanLocOneRun cfg₁1.memory cf₁.memory θ₁1 θ₁3 l :=
                  PreservesInheritedFinalCleanLocsOneRun.apply
                    (ctx := ctxForE3) (res := res3)
                    (μ_in := cfg₁1.memory) (μ_out := cf₁.memory)
                    (θ_in := θ₁1) (θ_out := θ₁3)
                    hpres₃ hlookup_mid_ctxForE3 hlookup3 hclean3
                have hagree_mid :
                    agreeLocUnder predSat res1.regime'
                      cfg₀1.memory cfg₁1.memory θ₀1 θ₁1 (l, qt_mid) :=
                  hagree1.1 l qt_mid (by simpa [ctxAfter] using hlookup_mid) hclean_mid
                cases hagree_mid with
                | both_unrealized _ _ hnone₀ hnone₁ =>
                    have hnone₀' : θ₀2.lookup l = none := by
                      cases hpres_l₀ with
                      | both_unrealized _ hnone_out =>
                          exact hnone_out
                      | preserve_value _ _ hsome_in _ _ _ =>
                          exact nomatch (hnone₀.symm.trans hsome_in)
                    have hnone₁' : θ₁3.lookup l = none := by
                      cases hpres_l₁ with
                      | both_unrealized _ hnone_out =>
                          exact hnone_out
                      | preserve_value _ _ hsome_in _ _ _ =>
                          exact nomatch (hnone₁.symm.trans hsome_in)
                    exact agreeLocUnder.both_unrealized l qt hnone₀' hnone₁'
                | agree_values _ _ a₀m a₁m n₀ n₁ hreal₀m hreal₁m hmem₀m hmem₁m hagreeVmid =>
                    cases hpres_l₀ with
                    | both_unrealized hnone_in _ =>
                        exact nomatch (hreal₀m.symm.trans hnone_in)
                    | preserve_value a₀' n₀' hθ₀in hμ₀in hθ₀out hμ₀out =>
                        cases hpres_l₁ with
                        | both_unrealized hnone_in _ =>
                            exact nomatch (hreal₁m.symm.trans hnone_in)
                        | preserve_value a₁' n₁' hθ₁in hμ₁in hθ₁out hμ₁out =>
                            have ha₀ : a₀' = a₀m := by
                              exact Option.some.inj (hθ₀in.symm.trans hreal₀m)
                            have hn₀ : n₀' = n₀ := by
                              rw [ha₀] at hμ₀in
                              exact Option.some.inj (hμ₀in.symm.trans hmem₀m)
                            have ha₁ : a₁' = a₁m := by
                              exact Option.some.inj (hθ₁in.symm.trans hreal₁m)
                            have hn₁ : n₁' = n₁ := by
                              rw [ha₁] at hμ₁in
                              exact Option.some.inj (hμ₁in.symm.trans hmem₁m)
                            cases ha₀
                            cases hn₀
                            cases ha₁
                            cases hn₁
                            have hnotref_mid : ¬ ∃ ls, qt_mid.etyp = ETyp.ref ls := by
                              intro ⟨ls, hls⟩
                              rw [memEnv_lookup_etyp_int res1.memEnv' l qt_mid hlookup_mid] at hls
                              simp at hls
                            have hnotfun_mid : qt_mid.etyp.isFunctionType = false := by
                              rw [memEnv_lookup_etyp_int res1.memEnv' l qt_mid hlookup_mid]
                              decide
                            have hEq_vals : Value.num n₀ = Value.num n₁ :=
                              agreeValueUnder_nonref_eq_of_clean
                                hclean_mid hnotref_mid hnotfun_mid hagreeVmid
                            have hnotref_final : ¬ ∃ ls, qt.etyp = ETyp.ref ls := by
                              intro ⟨ls, hls⟩
                              rw [memEnv_lookup_etyp_int (ctxAfter ctxᵢ res).memEnv l qt hlookup] at hls
                              simp at hls
                            have hagreeV_final :
                                agreeValueUnder predSat res.regime'
                                  cf₀.memory cf₁.memory θ₀2 θ₁3 qt (Value.num n₀) (Value.num n₁) := by
                              cases hclean with
                              | clean hpoison =>
                                  have hnotfun_final : qt.etyp.isFunctionType = false := by
                                    rw [memEnv_lookup_etyp_int (ctxAfter ctxᵢ res).memEnv l qt hlookup]
                                    decide
                                  exact
                                    agreeValueUnder.clean_eq_nonref_nonarrow
                                      hpoison hnotfun_final hnotref_final hEq_vals
                              | guard k htag hk hnotfun =>
                                  exact
                                    agreeValueUnder.withPred_true_eq
                                      k htag hk hnotfun hnotref_final hEq_vals
                            exact
                              agreeLocUnder.agree_values
                                l qt a₀m a₁m n₀ n₁
                                hθ₀out hθ₁out hμ₀out hμ₁out hagreeV_final
              · -- FRESH: l ∉ res1.memEnv' → both θ unrealized
                have hnotContains_ctx'' : ¬ ctx''.memEnv.contains l := by
                  simpa [ctx'', ctx'] using hcontains_mid
                have hnotContains_ctxForE3 : ¬ ctxForE3.memEnv.contains l := by
                  simpa [ctxForE3, ctx'', ctx'] using hcontains_mid
                -- θ₀2: run 0 executes e2
                have hθ₀2_none : θ₀2.lookup l = none := by
                  by_cases hc2 : res2.memEnv'.contains l
                  · -- l ∈ res2: use FreshCleanLocsUnrealizedOneRun
                    rcases memEnv_lookup_some_of_contains res2.memEnv' l hc2 with ⟨qt2, hlookup2⟩
                    have hclean2 : qtypCleanUnder res2.regime' qt2 := by
                      cases hclean with
                      | clean hpoison_out =>
                          have henv2 : res2.memEnv'.lookup l ≠ none := by
                            intro hnone; rw [hlookup2] at hnone; contradiction
                          rcases
                              joinMemEnvsStrong_lookup_clean_left
                                res2.memEnv' res3.memEnv' l qt
                                hlookup_join hpoison_out henv2
                            with ⟨qt2', hlookup2', _hetyp2, hpoison2⟩
                          have hqt2 : qt2 = qt2' := by
                            rw [hlookup2] at hlookup2'; injection hlookup2'
                          cases hqt2
                          exact qtypCleanUnder.clean hpoison2
                      | guard k htag hk hnotfun =>
                          have hk_join :
                              (joinRegimes res2.regime' res3.regime').lookup? k = some true := by
                            simpa [ctxAfter, hregime'] using hk
                          have htag2 : qtypGuardTag qt2 = some k :=
                            joinMemEnvsStrong_lookup_guardTag_left
                              res2.memEnv' res3.memEnv' l qt qt2 k
                              hlookup_join hlookup2 htag
                          have hk2 : res2.regime'.lookup? k = some true :=
                            joinRegimes_lookup_some_left
                              res2.regime' res3.regime' k true hk_join
                          have hnotfun2 : qt2.etyp.isFunctionType = false := by
                            rw [memEnv_lookup_etyp_int res2.memEnv' l qt2 hlookup2]
                            decide
                          exact qtypCleanUnder.guard k htag2 hk2 hnotfun2
                    exact _hfresh₂ l qt2 hnotContains_ctx'' hlookup2 hclean2
                  · -- l ∉ res2: θ₀2 can't map l
                    exact theta_not_contains_if_not_in_memEnv
                      (ctxAfter ctx'' res2) cf₀.memory cf₀.varEnv θ₀2 l
                      hric₀2 (by simpa [ctxAfter] using hc2)
                -- θ₁3: run 1 executes e3
                have hθ₁3_none : θ₁3.lookup l = none := by
                  by_cases hc3 : res3.memEnv'.contains l
                  · -- l ∈ res3: use FreshCleanLocsUnrealizedOneRun
                    rcases memEnv_lookup_some_of_contains res3.memEnv' l hc3 with ⟨qt3, hlookup3⟩
                    have hclean3 : qtypCleanUnder res3.regime' qt3 := by
                      cases hclean with
                      | clean hpoison_out =>
                          have henv3 : res3.memEnv'.lookup l ≠ none := by
                            intro hnone; rw [hlookup3] at hnone; contradiction
                          rcases
                              joinMemEnvsStrong_lookup_clean_right
                                res2.memEnv' res3.memEnv' l qt
                                hlookup_join hpoison_out henv3
                            with ⟨qt3', hlookup3', _hetyp3, hpoison3⟩
                          have hqt3 : qt3 = qt3' := by
                            rw [hlookup3] at hlookup3'; injection hlookup3'
                          cases hqt3
                          exact qtypCleanUnder.clean hpoison3
                      | guard k htag hk hnotfun =>
                          have hk_join :
                              (joinRegimes res2.regime' res3.regime').lookup? k = some true := by
                            simpa [ctxAfter, hregime'] using hk
                          have htag3 : qtypGuardTag qt3 = some k :=
                            joinMemEnvsStrong_lookup_guardTag_right
                              res2.memEnv' res3.memEnv' l qt qt3 k
                              hlookup_join hlookup3 htag
                          have hk3 : res3.regime'.lookup? k = some true :=
                            joinRegimes_lookup_some_right
                              res2.regime' res3.regime' k true hk_join
                          have hnotfun3 : qt3.etyp.isFunctionType = false := by
                            rw [memEnv_lookup_etyp_int res3.memEnv' l qt3 hlookup3]
                            decide
                          exact qtypCleanUnder.guard k htag3 hk3 hnotfun3
                    exact _hfresh₃ l qt3 hnotContains_ctxForE3 hlookup3 hclean3
                  · -- l ∉ res3: θ₁3 can't map l
                    exact theta_not_contains_if_not_in_memEnv
                      (ctxAfter ctxForE3 res3) cf₁.memory cf₁.varEnv θ₁3 l
                      (by simpa [ctxAfter, ctxForE3, ctx'', ctx', pc'] using hric₁3)
                      (by simpa [ctxAfter] using hc3)
                exact agreeLocUnder.both_unrealized l qt hθ₀2_none hθ₁3_none
            · intro x qt hlookup hclean
              -- ite leaves varEnv untouched, so `qt`'s tags are bounded by `ctxᵢ.nextTag`
              -- and hence by `res1.nextTag'` (nextTag monotone).  This discharges freshness
              -- for the extended-regime backward clean/value transports below.
              have hlookup_ctxᵢ : ctxᵢ.varEnv.lookup x = some qt := by
                simpa [ctxAfter] using hlookup
              have hbge1 : ctxᵢ.nextTag ≤ res1.nextTag' :=
                typecheck_nextTag_mono ctxᵢ e1 fuel' res1 htc1'
              have hqt_pred1 : qtypPredTagBounded qt res1.nextTag' :=
                qtypPredTagBounded_mono
                  (TagBoundedCtx_varEnv_predTagBounded htagBounded hlookup_ctxᵢ) hbge1
              have hqt_bound1 : etypClosuresFullBounded qt.etyp res1.nextTag' :=
                etypClosuresFullBounded_mono
                  (TagBoundedCtx_varEnv_etypClosures htagBounded hlookup_ctxᵢ) hbge1
              have hclean_mid : qtypCleanUnder res1.regime' qt :=
                cleanUnder_of_monotoneExt h_mono_final (fun _ hk => hk) hqt_pred1 hclean
              have hagree_mid :
                  agreeVarUnder predSat res1.regime'
                    cfg₀1.memory cfg₀1.varEnv cfg₁1.memory cfg₁1.varEnv θ₀1 θ₁1 (x, qt) :=
                hagree1.2 x qt (by simpa [ctxAfter] using hlookup) hclean_mid
              cases hagree_mid with
              | both_none _ _ hnone₀ hnone₁ =>
                  exact
                    agreeVarUnder.both_none x qt
                      (by simpa [hvar_cf₀] using hnone₀)
                      (by simpa [hvar_cf₁] using hnone₁)
              | agree_values _ _ v₀ v₁ hlookup₀ hlookup₁ hagreeVmid =>
                  -- The regime first, at the state after the condition; then
                  -- across each run's branch, where every tag of the final
                  -- regime keeps its meaning (the frames from the step's start).
                  have hagreeV_ext :
                      agreeValueUnder predSat res.regime'
                        cfg₀1.memory cfg₁1.memory θ₀1 θ₁1 qt v₀ v₁ :=
                    agreeValueUnder_clean_transport_by_cleanBack_ext
                      h_mono_final (fun _ hk => hk) hqt_bound1 hclean hagreeVmid
                  have hS₀ : PredSatStable predSat tm res.regime' θ₀1 θ₀2
                      cfg₀1.memory cf₀.memory := by
                    simpa [ctxAfter] using
                      predSatStable_mid hpredlaws hfp.2 hM₀1 hM₀_case hF₀1 hF₀_case hRback
                  have hS₁ : PredSatStable predSat tm res.regime' θ₁1 θ₁3
                      cfg₁1.memory cf₁.memory := by
                    simpa [ctxAfter] using
                      predSatStable_mid hpredlaws hfp.2 hM₁1 hM₁_case hF₁1 hF₁_case hRback
                  have hagreeV_final :
                      agreeValueUnder predSat res.regime'
                        cf₀.memory cf₁.memory θ₀2 θ₁3 qt v₀ v₁ :=
                    agreeValueUnder_clean_extends_transport_mem hS₀ hS₁
                      (wfTagMeaningCtx_var_lookup_qtyp tm ctxᵢ x qt hwfTm hlookup_ctxᵢ)
                      hclean hθext₀2.1 hθext₁3.1 hagreeV_ext
                  exact
                    agreeVarUnder.agree_values x qt v₀ v₁
                      (by simpa [hvar_cf₀] using hlookup₀)
                      (by simpa [hvar_cf₁] using hlookup₁)
                      hagreeV_final
          have hvalc₀_join :
              valueConsistentWithRegime predSat
                (ctxAfter ctx'' resJoin).regime
                resJoin.qualType cf₀.memory θ₀2 o₀ := by
            exact
              joinTypeResults_transport_valueConsistentWithRegime_from_member
                (predSat := predSat)
                (ctx := ctx'') (first := res2) (src := res2) (rest := [res3]) (res := resJoin)
                (μ := cf₀.memory) (θ := θ₀2) (v := o₀)
                hjoin (by simp) hvalc₀2
          have hvalc₁_join :
              valueConsistentWithRegime predSat
                (ctxAfter ctx'' resJoin).regime
                resJoin.qualType cf₁.memory θ₁3 o₁ := by
            exact
              joinTypeResults_transport_valueConsistentWithRegime_from_member
                (predSat := predSat)
                (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                (μ := cf₁.memory) (θ := θ₁3) (v := o₁)
                hjoin (by simp) hvalc₁3
          have hvalc₀_final :
              valueConsistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                res.qualType cf₀.memory θ₀2 o₀ := by
            refine valueConsistentWithRegime.noTag ?_ ?_
            · simp [qtypGuardTag, hpredNo]
            · have hcap_join :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    resJoin.qualType cf₀.memory θ₀2 o₀ :=
                valueConsistentWithRegime_closureCapturedVarsRegime hvalc₀_join
              have hcap_res :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    res.qualType cf₀.memory θ₀2 o₀ :=
                closureCapturedVarsRegime_transport_etyp hresJoin_etyp hcap_join
              simpa [ctxAfter, ctx'', ctx', pc', resJoin, hregime'] using hcap_res
          have hvalc₁_final :
              valueConsistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                res.qualType cf₁.memory θ₁3 o₁ := by
            refine valueConsistentWithRegime.noTag ?_ ?_
            · simp [qtypGuardTag, hpredNo]
            · have hcap_join :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    resJoin.qualType cf₁.memory θ₁3 o₁ :=
                valueConsistentWithRegime_closureCapturedVarsRegime hvalc₁_join
              have hcap_res :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    res.qualType cf₁.memory θ₁3 o₁ :=
                closureCapturedVarsRegime_transport_etyp hresJoin_etyp hcap_join
              simpa [ctxAfter, ctx'', ctx', pc', resJoin, hregime'] using hcap_res
          have hwfcf₀_final : wfConfig cf₀ := by
            exact (wfConfig_preserved e2 _ cf₀ o₀
              ((terminatesTo_preserves_registry ht₀_e1).symm ▸ hOp)
              (hreg₀1.symm ▸ hres₀1.toBelow)
              ht₀_e2 hwfcf₀1).1
          have hwfcf₁_final : wfConfig cf₁ := by
            exact (wfConfig_preserved e3 _ cf₁ o₁
              ((terminatesTo_preserves_registry ht₁_e1).symm ▸ hOp)
              (hreg₁1.symm ▸ hres₁1.toBelow)
              ht₁_e3 hwfcf₁1).1
          have hres_poison_true : res.qualType.poison = true := by
            calc
              res.qualType.poison =
                  joinPoison ctxᵢ.pc
                    (joinPoison res1.qualType.poison
                      (joinPoison res2.qualType.poison res3.qualType.poison)) := hpoison
              _ = true := by
                have hpc_or : ctxᵢ.pc = true ∨ res1.qualType.poison = true := by
                  have hpc_res1 : joinPoison ctxᵢ.pc res1.qualType.poison = true := by
                    simpa [pc'] using hpc_true
                  cases hctx : ctxᵢ.pc <;> cases hp1 : res1.qualType.poison <;>
                    simp [joinPoison, hctx, hp1] at hpc_res1 ⊢
                cases hpc_or with
                | inl hctx =>
                    simp [joinPoison, hctx]
                | inr hp1 =>
                    simp [joinPoison, hp1]
          exact
            ⟨tmOut, BoundaryTagMeaningPost.of_isCanonical_predSat hcanonOut hpredlawsOut hwithinOut,
              hpredlawsOut, hresTm, θ₀2, θ₁3, hθext₀, hθext₁, hvtyp₀_final, hvtyp₁_final,
              hwfTm_final, hwf_final, htagBounded_final, hwfcf₀_final, hwfcf₁_final,
              hric₀_final, hric₁_final, htag_final,
              hcwr₀_final, hcwr₁_final, hagree_final,
              hvalc₀_final, hvalc₁_final,
              resultAgreesIfClean_of_poison_noPred hres_poison_true hpredNo,
              (by rw [hdecl']; exact ReservedDiscipline.mono_declared hsubE3' hrdS₀2),
              (by rw [hdecl']; exact hrdS₁3),
              hM₀_case, hM₁_case, hF₀_case, hF₁_case⟩
  | inr hbranch₀_false =>
      cases hbranch₁ with
      | inl hbranch₁_true =>
          have ht₀_e3 : terminatesTo e3 cfg₀1 cf₀ o₀ := hbranch₀_false.2
          have ht₁_e2 : terminatesTo e2 cfg₁1 cf₁ o₁ := hbranch₁_true.2
          have hpc_true : pc' = true := by
            cases hpc_val : pc' with
            | true =>
                rfl
            | false =>
                have hpoison1_false : res1.qualType.poison = false := by
                  have hjoin_false : joinPoison ctxᵢ.pc res1.qualType.poison = false := by
                    simpa [pc'] using hpc_val
                  exact (joinPoison_eq_false hjoin_false).2
                have hclean1 :
                    qtypCleanUnder (ctxAfter ctxᵢ res1).regime res1.qualType :=
                  qtypCleanUnder.clean hpoison1_false
                have hnotref1 : ¬ ∃ ls, res1.qualType.etyp = ETyp.ref ls := by
                  intro ⟨ls, hls⟩
                  simp [hbool] at hls
                have hnotfun1 : res1.qualType.etyp.isFunctionType = false := by
                  simp [hbool, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                have hEq_bool : Value.bool b₀ = Value.bool b₁ :=
                  agreeValueUnder_nonref_eq_of_clean
                    hclean1 hnotref1 hnotfun1 (hres_agree1 hclean1)
                cases hEq_bool
                simp [hbranch₀_false.1] at hbranch₁_true
          have hpc'' : ctx''.pc = true := by
            simpa [ctx'', pc'] using hpc_true
          have hpcForE3 : ctxForE3.pc = true := by
            simpa [ctxForE3, ctx'', pc'] using hpc_true
          have hsingle_e2 :
              StepFRSingleRunFinalCleanPcTrue ctx'' e2 res2 predSat tm1 fuel' (registry := registry) :=
            singleIH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
              e2 ctx'' (by simpa [ctx'', ctx', pc'] using hctxThen)
                hcan2 hwfTm_ctx'' hTmBounded_ctx'' res2 htc2'
          have hsingle_e3 :
              StepFRSingleRunFinalCleanPcTrue ctxForE3 e3 res3 predSat tm1 fuel' (registry := registry) :=
            singleIH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
              e3 ctxForE3 (by simpa [ctxForE3, ctx'', ctx', pc'] using hctxElse)
                hcan3 hwfTm_ctxForE3 hTmBounded_ctxForE3 res3 htc3'
          -- Thread extern registry for cfg₀1 and cfg₁1.
          have hreg_cfg₀1_s2 : cfg₀1.registry = registry := by
            simpa using terminatesTo_preserves_registry ht₀_e1
          have hreg_cfg₁1_s2 : cfg₁1.registry = registry := by
            simpa using terminatesTo_preserves_registry ht₁_e1
          have hcfg₀1_eq_s2 : cfg₀1 = { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry } :=
            config_eq_of_registry cfg₀1 registry hreg_cfg₀1_s2
          have hcfg₁1_eq_s2 : cfg₁1 = { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₁1.pureMode, registry := registry } :=
            config_eq_of_registry cfg₁1 registry hreg_cfg₁1_s2
          have ht₀_e3'' : terminatesTo e3 { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry } cf₀ o₀ := by
            rw [← hcfg₀1_eq_s2]; exact ht₀_e3
          have ht₁_e2'' : terminatesTo e2 { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₁1.pureMode, registry := registry } cf₁ o₁ := by
            rw [← hcfg₁1_eq_s2]; exact ht₁_e2
          have hwfcf₀1_s2 : wfConfig { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry } := by
            rw [← hcfg₀1_eq_s2]; exact hwfcf₀1
          have hwfcf₁1_s2 : wfConfig { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₁1.pureMode, registry := registry } := by
            rw [← hcfg₁1_eq_s2]; exact hwfcf₁1
          have hroot₀3s : P₀ ⟨ctxForE3, e3, fuel',
              { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry }⟩ := by
            rw [← hcfg₀1_eq_s2]
            exact hprem.run₀.closed hroot₀ (SubStep.iteElseStd (f := fuel') hstd htc1
              (by simpa [hbranch₀_false.1] using ht₀_e1) htc2)
          have hroot₁2s : P₁ ⟨ctx'', e2, fuel',
              { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₁1.pureMode, registry := registry }⟩ := by
            rw [← hcfg₁1_eq_s2]
            exact hprem.run₁.closed hroot₁ (SubStep.iteThenStd (f := fuel') hstd htc1
              (by simpa [hbranch₁_true.1] using ht₁_e1))
          rcases
              (hsingle_e3 hpredlaws1 (hframe'.skip hcanon1.within) hwfTm_ctxForE3
                hTmBounded_ctxForE3 htagBounded_ctxForE3 hfp_ctxForE3).2
                cfg₀1.memory cfg₀1.varEnv θ₀1 cf₀ o₀
                hθ₀1wf hwf_ctxForE3 hric₀1_ctxForE3 htagR_ctxForE3
                hcwr₀1_ctxForE3 cfg₀1.nextAddr cfg₀1.pureMode hwfcf₀1_s2 hres₀1 hrdStdE3₀ ht₀_e3'' hpcForE3
                hprem.run₀ hroot₀3s
            with ⟨θ₀3, hθext₀3, hvtyp₀3, hric₀3, hcwr₀3, hvalc₀3, hpres₃, _hfresh₃, hrdS₀3, hM₀3, hF₀3⟩
          rcases
              (hsingle_e2 hpredlaws1 (hframe'.left.next hcanon1.within) hwfTm_ctx''
                hTmBounded_ctx'' htagBounded_ctx'' hfp_ctx'').2
                cfg₁1.memory cfg₁1.varEnv θ₁1 cf₁ o₁
                hθ₁1wf hwf_ctx'' hric₁1_ctx'' htagR_ctx''
                hcwr₁1_ctx'' cfg₁1.nextAddr cfg₁1.pureMode hwfcf₁1_s2 hres₁1 hrdStd₁ ht₁_e2'' hpc''
                hprem.run₁ hroot₁2s
            with ⟨θ₁2, hθext₁2, hvtyp₁2, hric₁2, hcwr₁2, hvalc₁2, hpres₂, _hfresh₂, hrdS₁2, hM₁2, hF₁2⟩
          have hθext₀ : wfExtendsMap θ₀ θ₀3 := wfExtendsMap_trans hθext₀1 hθext₀3
          have hθext₁ : wfExtendsMap θ₁ θ₁2 := wfExtendsMap_trans hθext₁1 hθext₁2
          have hM₀_case : MapKeepsBelow ctxᵢ.nextLoc θ₀ θ₀3 := hM₀1.trans hM₀3 hnl_else
          have hM₁_case : MapKeepsBelow ctxᵢ.nextLoc θ₁ θ₁2 := hM₁1.trans hM₁2 hnl_then
          have hF₀_case : KeepsFootprints tm (ctxAfter ctxᵢ res).regime θ₀ μ₀ cf₀.memory :=
            KeepsFootprints.trans hF₀1 (KeepsFootprints.mono_regime hF₀3 hRright)
              hcanon1.extends_tm hθext₀1.1 hRback
          have hF₁_case : KeepsFootprints tm (ctxAfter ctxᵢ res).regime θ₁ μ₁ cf₁.memory :=
            KeepsFootprints.trans hF₁1 (KeepsFootprints.mono_regime hF₁2 hRleft)
              hcanon1.extends_tm hθext₁1.1 hRback
          have hric₀3_src :
              runtimeInstantiatesCtx (ctxAfter ctx'' res3) cf₀.memory cf₀.varEnv θ₀3 := by
            simpa [ctxAfter, ctxForE3, ctx'', ctx', pc'] using hric₀3
          have hcwr₀3_src :
              consistentWithRegime predSat
                (ctxAfter ctx'' res3).regime
                (ctxAfter ctx'' res3)
                cf₀.memory cf₀.varEnv θ₀3 := by
            simpa [ctxAfter, ctxForE3, ctx'', ctx', pc', consistentWithRegime] using hcwr₀3
          have hvar_cf₀ : cf₀.varEnv = cfg₀1.varEnv := by
            rcases ht₀_e3 with ⟨fuel₀w, verbose₀w, heval₀w⟩
            exact (beval_preserves_varEnv e3 fuel₀w verbose₀w cfg₀1 cf₀ o₀ heval₀w).symm
          have hvar_cf₁ : cf₁.varEnv = cfg₁1.varEnv := by
            rcases ht₁_e2 with ⟨fuel₁w, verbose₁w, heval₁w⟩
            exact (beval_preserves_varEnv e2 fuel₁w verbose₁w cfg₁1 cf₁ o₁ heval₁w).symm
          rcases typecheck_preserves_predSatLaws predSat tm ctxᵢ
              (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res
              hwfTm hTmBounded hframe htc with
            ⟨tmOut, hcanonOut, hpredlawsOut, hwithinOut⟩
          have hresTm : QTypRespectsTagMeaning tmOut res.qualType :=
            IsCanonicalExtension.respectsResult hcanonOut
          have hwfTm_final : wfTagMeaningCtx tmOut (ctxAfter ctxᵢ res) :=
            IsCanonicalExtension.wfCtx hcanonOut
          have hwf_final : wfTypeContext (ctxAfter ctxᵢ res) :=
            wfTypeContext_of_wfTypeResult ctxᵢ res
              (typecheckExpr_preserves_wfTypeResult
                ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res hwf htc)
              hwf (typecheck_nextLoc_mono ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res htc)
          have htagBounded_final : TagBoundedCtx (ctxAfter ctxᵢ res) :=
            typecheckExpr_preserves_TagBoundedCtx ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res (by simpa [typecheck] using htc) htagBounded
          have htag_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) :=
            typecheckExpr_preserves_regimeConsistentWithCtx
              ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res htagR htc
          have hvtyp₀_join : valueHasETyp θ₀3 o₀ resJoin.qualType.etyp := by
            exact
              joinTypeResults_transport_valueHasETyp_from_member
                (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                (θ := θ₀3) (v := o₀)
                hjoin (by simp) hvtyp₀3
          have hvtyp₁_join : valueHasETyp θ₁2 o₁ resJoin.qualType.etyp := by
            exact
              joinTypeResults_transport_valueHasETyp_from_member
                (ctx := ctx'') (first := res2) (src := res2) (rest := [res3]) (res := resJoin)
                (θ := θ₁2) (v := o₁)
                hjoin (by simp) hvtyp₁2
          have hvtyp₀_final : valueHasETyp θ₀3 o₀ res.qualType.etyp := by
            simpa [hresJoin_etyp] using hvtyp₀_join
          have hvtyp₁_final : valueHasETyp θ₁2 o₁ res.qualType.etyp := by
            simpa [hresJoin_etyp] using hvtyp₁_join
          have hric₀_final :
              runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀3 := by
            have hric₀_join :
                runtimeInstantiatesCtx (ctxAfter ctx'' resJoin) cf₀.memory cf₀.varEnv θ₀3 := by
              unfold runtimeInstantiatesCtx at hric₀3_src ⊢
              constructor
              · intro l a hθlookup
                rcases hric₀3_src.1 l a hθlookup with ⟨hcontains3, hmem⟩
                rcases
                    memEnv_lookup_some_of_contains
                      (ctxAfter ctx'' res3).memEnv l hcontains3
                  with ⟨qt3, hlookup3ctx⟩
                have hlookup3 : res3.memEnv'.lookup l = some qt3 := by
                  simpa [ctxAfter] using hlookup3ctx
                rcases
                    joinMemEnvsStrong_lookup_some_of_right_lookup
                      res2.memEnv' res3.memEnv' l qt3 hlookup3
                  with ⟨qt, hlookup_join⟩
                have hcontains_join :
                    (joinMemEnvsStrong res2.memEnv' res3.memEnv').contains l :=
                  memEnv_contains_of_lookup_some
                    (joinMemEnvsStrong res2.memEnv' res3.memEnv') l qt hlookup_join
                exact ⟨by simpa [ctxAfter] using hcontains_join, hmem⟩
              · intro x qt hlookup
                have hlookup' :
                    (ctxAfter ctx'' res3).varEnv.lookup x = some qt := by
                  simpa [ctxAfter, ctx'', ctx', pc'] using hlookup
                exact hric₀3_src.2 hlookup'
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using! hric₀_join
          have hric₁_final :
              runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
            have hric₁_join :
                runtimeInstantiatesCtx (ctxAfter ctx'' resJoin) cf₁.memory cf₁.varEnv θ₁2 := by
              refine
                ite_join_transport_runtimeInstantiatesCtx
                  (ctx := ctx'') (first := res2) (rest := [res3]) (res := resJoin)
                  (μ := cf₁.memory) (ρ := cf₁.varEnv) (θ := θ₁2)
                  hjoin ?_ hric₁2
              intro l hcontains
              rcases memEnv_lookup_some_of_contains res2.memEnv' l hcontains with ⟨qt2, hlookup2⟩
              rcases
                  joinMemEnvsStrong_lookup_some_of_left_lookup
                    res2.memEnv' res3.memEnv' l qt2 hlookup2
                with ⟨qt, hlookup_join⟩
              exact memEnv_contains_of_lookup_some _ _ _ hlookup_join
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using! hric₁_join
          have hcwr₀_final :
              consistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                (ctxAfter ctxᵢ res)
                cf₀.memory cf₀.varEnv θ₀3 := by
            have hcwr₀_join :
                consistentWithRegime predSat
                  (ctxAfter ctx'' resJoin).regime
                  (ctxAfter ctx'' resJoin)
                  cf₀.memory cf₀.varEnv θ₀3 := by
              exact
                consistentWithRegime_join_from_right
                  predSat ctx'' res2 res3 resJoin
                  cf₀.memory cf₀.varEnv θ₀3
                  rfl rfl hcwr₀3_src
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using! hcwr₀_join
          have hcwr₁_final :
              consistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                (ctxAfter ctxᵢ res)
                cf₁.memory cf₁.varEnv θ₁2 := by
            have hcwr₁_join :
                consistentWithRegime predSat
                  (ctxAfter ctx'' resJoin).regime
                  (ctxAfter ctx'' resJoin)
                  cf₁.memory cf₁.varEnv θ₁2 := by
              exact
                consistentWithRegime_join_from_left
                  predSat ctx'' res2 res3 resJoin
                  cf₁.memory cf₁.varEnv θ₁2
                  rfl rfl hcwr₁2
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using! hcwr₁_join
          have hagree_final :
              agreeOnClean predSat
                (ctxAfter ctxᵢ res).regime
                (ctxAfter ctxᵢ res)
                cf₀.memory cf₀.varEnv θ₀3 cf₁.memory cf₁.varEnv θ₁2 := by
            constructor
            · intro l qt hlookup hclean
              have hlookup_res : res.memEnv'.lookup l = some qt := by
                simpa [ctxAfter] using hlookup
              have hlookup_join :
                  (joinMemEnvsStrong res2.memEnv' res3.memEnv').lookup l = some qt := by
                simpa [hmemEnv] using hlookup_res
              -- Case split: l inherited from res1 vs. fresh
              by_cases hcontains_mid : res1.memEnv'.contains l
              · -- INHERITED: l ∈ res1.memEnv'
                rcases memEnv_lookup_some_of_contains res1.memEnv' l hcontains_mid with
                  ⟨qt_mid, hlookup_mid⟩
                have hclean_mid : qtypCleanUnder res1.regime' qt_mid := by
                  -- Trace clean back through e3 (which has ctxForE3.memEnv = res1.memEnv')
                  have hcontains_ctxForE3 : ctxForE3.memEnv.contains l := by
                    simpa [ctxForE3, ctx'', ctx'] using hcontains_mid
                  have hcontains3 : res3.memEnv'.contains l :=
                    typecheckExpr_mem_contains_preserved
                      ctxForE3 e3 fuel' res3
                      (by simpa [ctxForE3, ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using htc3)
                      l hcontains_ctxForE3
                  rcases memEnv_lookup_some_of_contains res3.memEnv' l hcontains3 with
                    ⟨qt3, hlookup3⟩
                  have hclean3 : qtypCleanUnder res3.regime' qt3 := by
                    cases hclean with
                    | clean hpoison_out =>
                        have henv3 : res3.memEnv'.lookup l ≠ none := by
                          intro hnone; rw [hlookup3] at hnone; contradiction
                        rcases
                            joinMemEnvsStrong_lookup_clean_right
                              res2.memEnv' res3.memEnv' l qt
                              hlookup_join hpoison_out henv3
                          with ⟨qt3', hlookup3', _hetyp3, hpoison3⟩
                        have hqt3 : qt3 = qt3' := by
                          rw [hlookup3] at hlookup3'; injection hlookup3'
                        cases hqt3
                        exact qtypCleanUnder.clean hpoison3
                    | guard k htag hk hnotfun =>
                        have hk_join :
                            (joinRegimes res2.regime' res3.regime').lookup? k = some true := by
                          simpa [ctxAfter, hregime'] using hk
                        have htag3 : qtypGuardTag qt3 = some k :=
                          joinMemEnvsStrong_lookup_guardTag_right
                            res2.memEnv' res3.memEnv' l qt qt3 k
                            hlookup_join hlookup3 htag
                        have hk3 : res3.regime'.lookup? k = some true :=
                          joinRegimes_lookup_some_right
                            res2.regime' res3.regime' k true hk_join
                        have hnotfun3 : qt3.etyp.isFunctionType = false := by
                          rw [memEnv_lookup_etyp_int res3.memEnv' l qt3 hlookup3]
                          decide
                        exact qtypCleanUnder.guard k htag3 hk3 hnotfun3
                  rcases
                      typecheckExpr_clean_lookup_origin_of_pc_true
                        ctxForE3 e3 fuel' res3 htc3' hwf_ctxForE3 htagBounded_ctxForE3 hpcForE3
                        l qt3 hlookup3 hcontains_ctxForE3 hclean3
                    with ⟨qt_in, hlookup_in, hclean_in⟩
                  have heq_qt : qt_mid = qt_in := by
                    have : ctxForE3.memEnv.lookup l = some qt_mid := by
                      simpa [ctxForE3, ctx'', ctx'] using hlookup_mid
                    rw [this] at hlookup_in; injection hlookup_in
                  subst heq_qt
                  exact hclean_in
                have hcontains2 : res2.memEnv'.contains l :=
                  typecheckExpr_mem_contains_preserved
                    ctx'' e2 fuel' res2
                    (by simpa [ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using htc2)
                    l
                    (by simpa [ctx'', ctx'] using hcontains_mid)
                have hcontains3 : res3.memEnv'.contains l :=
                  typecheckExpr_mem_contains_preserved
                    ctxForE3 e3 fuel' res3
                    (by simpa [ctxForE3, ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using htc3)
                    l
                    (by simpa [ctxForE3, ctx'', ctx'] using hcontains_mid)
                rcases memEnv_lookup_some_of_contains res2.memEnv' l hcontains2 with ⟨qt2, hlookup2⟩
                rcases memEnv_lookup_some_of_contains res3.memEnv' l hcontains3 with ⟨qt3, hlookup3⟩
                have hclean2 : qtypCleanUnder res2.regime' qt2 := by
                  cases hclean with
                  | clean hpoison_out =>
                      have henv2 : res2.memEnv'.lookup l ≠ none := by
                        intro hnone; rw [hlookup2] at hnone; contradiction
                      rcases
                          joinMemEnvsStrong_lookup_clean_left
                            res2.memEnv' res3.memEnv' l qt
                            hlookup_join hpoison_out henv2
                        with ⟨qt2', hlookup2', _hetyp2, hpoison2⟩
                      have hqt2 : qt2 = qt2' := by
                        rw [hlookup2] at hlookup2'; injection hlookup2'
                      cases hqt2
                      exact qtypCleanUnder.clean hpoison2
                  | guard k htag hk hnotfun =>
                      have hk_join :
                          (joinRegimes res2.regime' res3.regime').lookup? k = some true := by
                        simpa [ctxAfter, hregime'] using hk
                      have htag2 : qtypGuardTag qt2 = some k :=
                        joinMemEnvsStrong_lookup_guardTag_left
                          res2.memEnv' res3.memEnv' l qt qt2 k
                          hlookup_join hlookup2 htag
                      have hk2 : res2.regime'.lookup? k = some true :=
                        joinRegimes_lookup_some_left
                          res2.regime' res3.regime' k true hk_join
                      have hnotfun2 : qt2.etyp.isFunctionType = false := by
                        rw [memEnv_lookup_etyp_int res2.memEnv' l qt2 hlookup2]
                        decide
                      exact qtypCleanUnder.guard k htag2 hk2 hnotfun2
                have hclean3 : qtypCleanUnder res3.regime' qt3 := by
                  cases hclean with
                  | clean hpoison_out =>
                      have henv3 : res3.memEnv'.lookup l ≠ none := by
                        intro hnone; rw [hlookup3] at hnone; contradiction
                      rcases
                          joinMemEnvsStrong_lookup_clean_right
                            res2.memEnv' res3.memEnv' l qt
                            hlookup_join hpoison_out henv3
                        with ⟨qt3', hlookup3', _hetyp3, hpoison3⟩
                      have hqt3 : qt3 = qt3' := by
                        rw [hlookup3] at hlookup3'; injection hlookup3'
                      cases hqt3
                      exact qtypCleanUnder.clean hpoison3
                  | guard k htag hk hnotfun =>
                      have hk_join :
                          (joinRegimes res2.regime' res3.regime').lookup? k = some true := by
                        simpa [ctxAfter, hregime'] using hk
                      have htag3 : qtypGuardTag qt3 = some k :=
                        joinMemEnvsStrong_lookup_guardTag_right
                          res2.memEnv' res3.memEnv' l qt qt3 k
                          hlookup_join hlookup3 htag
                      have hk3 : res3.regime'.lookup? k = some true :=
                        joinRegimes_lookup_some_right
                          res2.regime' res3.regime' k true hk_join
                      have hnotfun3 : qt3.etyp.isFunctionType = false := by
                        rw [memEnv_lookup_etyp_int res3.memEnv' l qt3 hlookup3]
                        decide
                      exact qtypCleanUnder.guard k htag3 hk3 hnotfun3
                have hlookup_mid_ctx'' : ctx''.memEnv.lookup l = some qt_mid := by
                  simpa [ctx'', ctx'] using hlookup_mid
                have hlookup_mid_ctxForE3 : ctxForE3.memEnv.lookup l = some qt_mid := by
                  simpa [ctxForE3, ctx'', ctx'] using hlookup_mid
                have hpres_l₀ :
                    PreservesInheritedCleanLocOneRun cfg₀1.memory cf₀.memory θ₀1 θ₀3 l :=
                  PreservesInheritedFinalCleanLocsOneRun.apply
                    (ctx := ctxForE3) (res := res3)
                    (μ_in := cfg₀1.memory) (μ_out := cf₀.memory)
                    (θ_in := θ₀1) (θ_out := θ₀3)
                    hpres₃ hlookup_mid_ctxForE3 hlookup3 hclean3
                have hpres_l₁ :
                    PreservesInheritedCleanLocOneRun cfg₁1.memory cf₁.memory θ₁1 θ₁2 l :=
                  PreservesInheritedFinalCleanLocsOneRun.apply
                    (ctx := ctx'') (res := res2)
                    (μ_in := cfg₁1.memory) (μ_out := cf₁.memory)
                    (θ_in := θ₁1) (θ_out := θ₁2)
                    hpres₂ hlookup_mid_ctx'' hlookup2 hclean2
                have hagree_mid :
                    agreeLocUnder predSat res1.regime'
                      cfg₀1.memory cfg₁1.memory θ₀1 θ₁1 (l, qt_mid) :=
                  hagree1.1 l qt_mid (by simpa [ctxAfter] using hlookup_mid) hclean_mid
                cases hagree_mid with
                | both_unrealized _ _ hnone₀ hnone₁ =>
                    have hnone₀' : θ₀3.lookup l = none := by
                      cases hpres_l₀ with
                      | both_unrealized _ hnone_out =>
                          exact hnone_out
                      | preserve_value _ _ hsome_in _ _ _ =>
                          exact nomatch (hnone₀.symm.trans hsome_in)
                    have hnone₁' : θ₁2.lookup l = none := by
                      cases hpres_l₁ with
                      | both_unrealized _ hnone_out =>
                          exact hnone_out
                      | preserve_value _ _ hsome_in _ _ _ =>
                          exact nomatch (hnone₁.symm.trans hsome_in)
                    exact agreeLocUnder.both_unrealized l qt hnone₀' hnone₁'
                | agree_values _ _ a₀m a₁m n₀ n₁ hreal₀m hreal₁m hmem₀m hmem₁m hagreeVmid =>
                    cases hpres_l₀ with
                    | both_unrealized hnone_in _ =>
                        exact nomatch (hreal₀m.symm.trans hnone_in)
                    | preserve_value a₀' n₀' hθ₀in hμ₀in hθ₀out hμ₀out =>
                        cases hpres_l₁ with
                        | both_unrealized hnone_in _ =>
                            exact nomatch (hreal₁m.symm.trans hnone_in)
                        | preserve_value a₁' n₁' hθ₁in hμ₁in hθ₁out hμ₁out =>
                            have ha₀ : a₀' = a₀m := by
                              exact Option.some.inj (hθ₀in.symm.trans hreal₀m)
                            have hn₀ : n₀' = n₀ := by
                              rw [ha₀] at hμ₀in
                              exact Option.some.inj (hμ₀in.symm.trans hmem₀m)
                            have ha₁ : a₁' = a₁m := by
                              exact Option.some.inj (hθ₁in.symm.trans hreal₁m)
                            have hn₁ : n₁' = n₁ := by
                              rw [ha₁] at hμ₁in
                              exact Option.some.inj (hμ₁in.symm.trans hmem₁m)
                            cases ha₀
                            cases hn₀
                            cases ha₁
                            cases hn₁
                            have hnotref_mid : ¬ ∃ ls, qt_mid.etyp = ETyp.ref ls := by
                              intro ⟨ls, hls⟩
                              rw [memEnv_lookup_etyp_int res1.memEnv' l qt_mid hlookup_mid] at hls
                              simp at hls
                            have hnotfun_mid : qt_mid.etyp.isFunctionType = false := by
                              rw [memEnv_lookup_etyp_int res1.memEnv' l qt_mid hlookup_mid]
                              decide
                            have hEq_vals : Value.num n₀ = Value.num n₁ :=
                              agreeValueUnder_nonref_eq_of_clean
                                hclean_mid hnotref_mid hnotfun_mid hagreeVmid
                            have hnotref_final : ¬ ∃ ls, qt.etyp = ETyp.ref ls := by
                              intro ⟨ls, hls⟩
                              rw [memEnv_lookup_etyp_int (ctxAfter ctxᵢ res).memEnv l qt hlookup] at hls
                              simp at hls
                            have hagreeV_final :
                                agreeValueUnder predSat res.regime'
                                  cf₀.memory cf₁.memory θ₀3 θ₁2 qt (Value.num n₀) (Value.num n₁) := by
                              cases hclean with
                              | clean hpoison =>
                                  have hnotfun_final : qt.etyp.isFunctionType = false := by
                                    rw [memEnv_lookup_etyp_int (ctxAfter ctxᵢ res).memEnv l qt hlookup]
                                    decide
                                  exact
                                    agreeValueUnder.clean_eq_nonref_nonarrow
                                      hpoison hnotfun_final hnotref_final hEq_vals
                              | guard k htag hk hnotfun =>
                                  exact
                                    agreeValueUnder.withPred_true_eq
                                      k htag hk hnotfun hnotref_final hEq_vals
                            exact
                              agreeLocUnder.agree_values
                                l qt a₀m a₁m n₀ n₁
                                hθ₀out hθ₁out hμ₀out hμ₁out hagreeV_final
              · -- FRESH: l ∉ res1.memEnv' → both θ unrealized
                have hnotContains_ctx'' : ¬ ctx''.memEnv.contains l := by
                  simpa [ctx'', ctx'] using hcontains_mid
                have hnotContains_ctxForE3 : ¬ ctxForE3.memEnv.contains l := by
                  simpa [ctxForE3, ctx'', ctx'] using hcontains_mid
                -- θ₀3: run 0 executes e3
                have hθ₀3_none : θ₀3.lookup l = none := by
                  by_cases hc3 : res3.memEnv'.contains l
                  · -- l ∈ res3: use FreshCleanLocsUnrealizedOneRun
                    rcases memEnv_lookup_some_of_contains res3.memEnv' l hc3 with ⟨qt3, hlookup3⟩
                    have hclean3 : qtypCleanUnder res3.regime' qt3 := by
                      cases hclean with
                      | clean hpoison_out =>
                          have henv3 : res3.memEnv'.lookup l ≠ none := by
                            intro hnone; rw [hlookup3] at hnone; contradiction
                          rcases
                              joinMemEnvsStrong_lookup_clean_right
                                res2.memEnv' res3.memEnv' l qt
                                hlookup_join hpoison_out henv3
                            with ⟨qt3', hlookup3', _hetyp3, hpoison3⟩
                          have hqt3 : qt3 = qt3' := by
                            rw [hlookup3] at hlookup3'; injection hlookup3'
                          cases hqt3
                          exact qtypCleanUnder.clean hpoison3
                      | guard k htag hk hnotfun =>
                          have hk_join :
                              (joinRegimes res2.regime' res3.regime').lookup? k = some true := by
                            simpa [ctxAfter, hregime'] using hk
                          have htag3 : qtypGuardTag qt3 = some k :=
                            joinMemEnvsStrong_lookup_guardTag_right
                              res2.memEnv' res3.memEnv' l qt qt3 k
                              hlookup_join hlookup3 htag
                          have hk3 : res3.regime'.lookup? k = some true :=
                            joinRegimes_lookup_some_right
                              res2.regime' res3.regime' k true hk_join
                          have hnotfun3 : qt3.etyp.isFunctionType = false := by
                            rw [memEnv_lookup_etyp_int res3.memEnv' l qt3 hlookup3]
                            decide
                          exact qtypCleanUnder.guard k htag3 hk3 hnotfun3
                    exact _hfresh₃ l qt3 hnotContains_ctxForE3 hlookup3 hclean3
                  · -- l ∉ res3: θ₀3 can't map l
                    exact theta_not_contains_if_not_in_memEnv
                      (ctxAfter ctxForE3 res3) cf₀.memory cf₀.varEnv θ₀3 l
                      hric₀3 (by simpa [ctxAfter] using hc3)
                -- θ₁2: run 1 executes e2
                have hθ₁2_none : θ₁2.lookup l = none := by
                  by_cases hc2 : res2.memEnv'.contains l
                  · -- l ∈ res2: use FreshCleanLocsUnrealizedOneRun
                    rcases memEnv_lookup_some_of_contains res2.memEnv' l hc2 with ⟨qt2, hlookup2⟩
                    have hclean2 : qtypCleanUnder res2.regime' qt2 := by
                      cases hclean with
                      | clean hpoison_out =>
                          have henv2 : res2.memEnv'.lookup l ≠ none := by
                            intro hnone; rw [hlookup2] at hnone; contradiction
                          rcases
                              joinMemEnvsStrong_lookup_clean_left
                                res2.memEnv' res3.memEnv' l qt
                                hlookup_join hpoison_out henv2
                            with ⟨qt2', hlookup2', _hetyp2, hpoison2⟩
                          have hqt2 : qt2 = qt2' := by
                            rw [hlookup2] at hlookup2'; injection hlookup2'
                          cases hqt2
                          exact qtypCleanUnder.clean hpoison2
                      | guard k htag hk hnotfun =>
                          have hk_join :
                              (joinRegimes res2.regime' res3.regime').lookup? k = some true := by
                            simpa [ctxAfter, hregime'] using hk
                          have htag2 : qtypGuardTag qt2 = some k :=
                            joinMemEnvsStrong_lookup_guardTag_left
                              res2.memEnv' res3.memEnv' l qt qt2 k
                              hlookup_join hlookup2 htag
                          have hk2 : res2.regime'.lookup? k = some true :=
                            joinRegimes_lookup_some_left
                              res2.regime' res3.regime' k true hk_join
                          have hnotfun2 : qt2.etyp.isFunctionType = false := by
                            rw [memEnv_lookup_etyp_int res2.memEnv' l qt2 hlookup2]
                            decide
                          exact qtypCleanUnder.guard k htag2 hk2 hnotfun2
                    exact _hfresh₂ l qt2 hnotContains_ctx'' hlookup2 hclean2
                  · -- l ∉ res2: θ₁2 can't map l
                    exact theta_not_contains_if_not_in_memEnv
                      (ctxAfter ctx'' res2) cf₁.memory cf₁.varEnv θ₁2 l
                      hric₁2 (by simpa [ctxAfter] using hc2)
                exact agreeLocUnder.both_unrealized l qt hθ₀3_none hθ₁2_none
            · intro x qt hlookup hclean
              -- ite leaves varEnv untouched, so `qt`'s tags are bounded by `ctxᵢ.nextTag`
              -- and hence by `res1.nextTag'` (nextTag monotone).  This discharges freshness
              -- for the extended-regime backward clean/value transports below.
              have hlookup_ctxᵢ : ctxᵢ.varEnv.lookup x = some qt := by
                simpa [ctxAfter] using hlookup
              have hbge1 : ctxᵢ.nextTag ≤ res1.nextTag' :=
                typecheck_nextTag_mono ctxᵢ e1 fuel' res1 htc1'
              have hqt_pred1 : qtypPredTagBounded qt res1.nextTag' :=
                qtypPredTagBounded_mono
                  (TagBoundedCtx_varEnv_predTagBounded htagBounded hlookup_ctxᵢ) hbge1
              have hqt_bound1 : etypClosuresFullBounded qt.etyp res1.nextTag' :=
                etypClosuresFullBounded_mono
                  (TagBoundedCtx_varEnv_etypClosures htagBounded hlookup_ctxᵢ) hbge1
              have hclean_mid : qtypCleanUnder res1.regime' qt :=
                cleanUnder_of_monotoneExt h_mono_final (fun _ hk => hk) hqt_pred1 hclean
              have hagree_mid :
                  agreeVarUnder predSat res1.regime'
                    cfg₀1.memory cfg₀1.varEnv cfg₁1.memory cfg₁1.varEnv θ₀1 θ₁1 (x, qt) :=
                hagree1.2 x qt (by simpa [ctxAfter] using hlookup) hclean_mid
              cases hagree_mid with
              | both_none _ _ hnone₀ hnone₁ =>
                  exact
                    agreeVarUnder.both_none x qt
                      (by simpa [hvar_cf₀] using hnone₀)
                      (by simpa [hvar_cf₁] using hnone₁)
              | agree_values _ _ v₀ v₁ hlookup₀ hlookup₁ hagreeVmid =>
                  -- The regime first, at the state after the condition; then
                  -- across each run's branch, where every tag of the final
                  -- regime keeps its meaning (the frames from the step's start).
                  have hagreeV_ext :
                      agreeValueUnder predSat res.regime'
                        cfg₀1.memory cfg₁1.memory θ₀1 θ₁1 qt v₀ v₁ :=
                    agreeValueUnder_clean_transport_by_cleanBack_ext
                      h_mono_final (fun _ hk => hk) hqt_bound1 hclean hagreeVmid
                  have hS₀ : PredSatStable predSat tm res.regime' θ₀1 θ₀3
                      cfg₀1.memory cf₀.memory := by
                    simpa [ctxAfter] using
                      predSatStable_mid hpredlaws hfp.2 hM₀1 hM₀_case hF₀1 hF₀_case hRback
                  have hS₁ : PredSatStable predSat tm res.regime' θ₁1 θ₁2
                      cfg₁1.memory cf₁.memory := by
                    simpa [ctxAfter] using
                      predSatStable_mid hpredlaws hfp.2 hM₁1 hM₁_case hF₁1 hF₁_case hRback
                  have hagreeV_final :
                      agreeValueUnder predSat res.regime'
                        cf₀.memory cf₁.memory θ₀3 θ₁2 qt v₀ v₁ :=
                    agreeValueUnder_clean_extends_transport_mem hS₀ hS₁
                      (wfTagMeaningCtx_var_lookup_qtyp tm ctxᵢ x qt hwfTm hlookup_ctxᵢ)
                      hclean hθext₀3.1 hθext₁2.1 hagreeV_ext
                  exact
                    agreeVarUnder.agree_values x qt v₀ v₁
                      (by simpa [hvar_cf₀] using hlookup₀)
                      (by simpa [hvar_cf₁] using hlookup₁)
                      hagreeV_final
          have hvalc₀_join :
              valueConsistentWithRegime predSat
                (ctxAfter ctx'' resJoin).regime
                resJoin.qualType cf₀.memory θ₀3 o₀ := by
            exact
              joinTypeResults_transport_valueConsistentWithRegime_from_member
                (predSat := predSat)
                (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                (μ := cf₀.memory) (θ := θ₀3) (v := o₀)
                hjoin (by simp) hvalc₀3
          have hvalc₁_join :
              valueConsistentWithRegime predSat
                (ctxAfter ctx'' resJoin).regime
                resJoin.qualType cf₁.memory θ₁2 o₁ := by
            exact
              joinTypeResults_transport_valueConsistentWithRegime_from_member
                (predSat := predSat)
                (ctx := ctx'') (first := res2) (src := res2) (rest := [res3]) (res := resJoin)
                (μ := cf₁.memory) (θ := θ₁2) (v := o₁)
                hjoin (by simp) hvalc₁2
          have hvalc₀_final :
              valueConsistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                res.qualType cf₀.memory θ₀3 o₀ := by
            refine valueConsistentWithRegime.noTag ?_ ?_
            · simp [qtypGuardTag, hpredNo]
            · have hcap_join :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    resJoin.qualType cf₀.memory θ₀3 o₀ :=
                valueConsistentWithRegime_closureCapturedVarsRegime hvalc₀_join
              have hcap_res :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    res.qualType cf₀.memory θ₀3 o₀ :=
                closureCapturedVarsRegime_transport_etyp hresJoin_etyp hcap_join
              simpa [ctxAfter, ctx'', ctx', pc', resJoin, hregime'] using hcap_res
          have hvalc₁_final :
              valueConsistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                res.qualType cf₁.memory θ₁2 o₁ := by
            refine valueConsistentWithRegime.noTag ?_ ?_
            · simp [qtypGuardTag, hpredNo]
            · have hcap_join :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    resJoin.qualType cf₁.memory θ₁2 o₁ :=
                valueConsistentWithRegime_closureCapturedVarsRegime hvalc₁_join
              have hcap_res :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    res.qualType cf₁.memory θ₁2 o₁ :=
                closureCapturedVarsRegime_transport_etyp hresJoin_etyp hcap_join
              simpa [ctxAfter, ctx'', ctx', pc', resJoin, hregime'] using hcap_res
          have hwfcf₀_final : wfConfig cf₀ := by
            exact (wfConfig_preserved e3 _ cf₀ o₀
              ((terminatesTo_preserves_registry ht₀_e1).symm ▸ hOp)
              (hreg₀1.symm ▸ hres₀1.toBelow)
              ht₀_e3 hwfcf₀1).1
          have hwfcf₁_final : wfConfig cf₁ := by
            exact (wfConfig_preserved e2 _ cf₁ o₁
              ((terminatesTo_preserves_registry ht₁_e1).symm ▸ hOp)
              (hreg₁1.symm ▸ hres₁1.toBelow)
              ht₁_e2 hwfcf₁1).1
          have hres_poison_true : res.qualType.poison = true := by
            calc
              res.qualType.poison =
                  joinPoison ctxᵢ.pc
                    (joinPoison res1.qualType.poison
                      (joinPoison res2.qualType.poison res3.qualType.poison)) := hpoison
              _ = true := by
                have hpc_or : ctxᵢ.pc = true ∨ res1.qualType.poison = true := by
                  have hpc_res1 : joinPoison ctxᵢ.pc res1.qualType.poison = true := by
                    simpa [pc'] using hpc_true
                  cases hctx : ctxᵢ.pc <;> cases hp1 : res1.qualType.poison <;>
                    simp [joinPoison, hctx, hp1] at hpc_res1 ⊢
                cases hpc_or with
                | inl hctx =>
                    simp [joinPoison, hctx]
                | inr hp1 =>
                    simp [joinPoison, hp1]
          exact
            ⟨tmOut, BoundaryTagMeaningPost.of_isCanonical_predSat hcanonOut hpredlawsOut hwithinOut,
              hpredlawsOut, hresTm, θ₀3, θ₁2, hθext₀, hθext₁, hvtyp₀_final, hvtyp₁_final,
              hwfTm_final, hwf_final, htagBounded_final, hwfcf₀_final, hwfcf₁_final,
              hric₀_final, hric₁_final, htag_final,
              hcwr₀_final, hcwr₁_final, hagree_final,
              hvalc₀_final, hvalc₁_final,
              resultAgreesIfClean_of_poison_noPred hres_poison_true hpredNo,
              (by rw [hdecl']; exact hrdS₀3),
              (by rw [hdecl']; exact ReservedDiscipline.mono_declared hsubE3' hrdS₁2),
              hM₀_case, hM₁_case, hF₀_case, hF₁_case⟩
      | inr hbranch₁_false =>
          have ht₀_e3 : terminatesTo e3 cfg₀1 cf₀ o₀ := hbranch₀_false.2
          have ht₁_e3 : terminatesTo e3 cfg₁1 cf₁ o₁ := hbranch₁_false.2
          have hpm_eq : cfg₁1.pureMode = cfg₀1.pureMode := by
            rw [hpm₀1, hpm₁1]
          have hcfg₁1_eq :
              cfg₁1 =
                { memory := cfg₁1.memory
                , varEnv := cfg₁1.varEnv
                , nextAddr := cfg₁1.nextAddr
                , pureMode := cfg₀1.pureMode, registry := registry } := by
            have hreg_cfg₁1_local : cfg₁1.registry = registry := by
              simpa using terminatesTo_preserves_registry ht₁_e1
            cases cfg₁1 with
            | mk m v n pm r =>
              simp only [Config.mk.injEq, true_and]
              refine ⟨hpm_eq, ?_⟩
              simpa using hreg_cfg₁1_local
          have ht₁_e3' : terminatesTo e3
              { memory := cfg₁1.memory
              , varEnv := cfg₁1.varEnv
              , nextAddr := cfg₁1.nextAddr
              , pureMode := cfg₀1.pureMode, registry := registry }
              cf₁ o₁ := by
            rw [← hcfg₁1_eq]
            exact ht₁_e3
          have hwfcf₁1' : wfConfig
              { memory := cfg₁1.memory
              , varEnv := cfg₁1.varEnv
              , nextAddr := cfg₁1.nextAddr
              , pureMode := cfg₀1.pureMode, registry := registry } := by
            rw [← hcfg₁1_eq]
            exact hwfcf₁1
          have hIH_e3 :=
            IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
              e3 ctxForE3 (by simpa [ctxForE3, ctx'', ctx', pc'] using hctxElse)
                hcan3 hwfTm_ctxForE3 htagBounded_ctxForE3 res3 htc3'
          -- Thread extern registry for cfg₀1.
          have hreg_cfg₀1_e3m : cfg₀1.registry = registry := by
            simpa using terminatesTo_preserves_registry ht₀_e1
          have hcfg₀1_eq_e3m : cfg₀1 = { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry } :=
            config_eq_of_registry cfg₀1 registry hreg_cfg₀1_e3m
          have ht₀_e3'' : terminatesTo e3 { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry } cf₀ o₀ := by
            rw [← hcfg₀1_eq_e3m]; exact ht₀_e3
          have hwfcf₀1'_e3m : wfConfig { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry } := by
            rw [← hcfg₀1_eq_e3m]; exact hwfcf₀1
          have hroot₀3 : P₀ ⟨ctxForE3, e3, fuel',
              { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry }⟩ := by
            rw [← hcfg₀1_eq_e3m]
            exact hprem.run₀.closed hroot₀ (SubStep.iteElseStd (f := fuel') hstd htc1
              (by simpa [hbranch₀_false.1] using ht₀_e1) htc2)
          have hroot₁3 : P₁ ⟨ctxForE3, e3, fuel',
              { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry }⟩ := by
            rw [← hcfg₁1_eq]
            exact hprem.run₁.closed hroot₁ (SubStep.iteElseStd (f := fuel') hstd htc1
              (by simpa [hbranch₁_false.1] using ht₁_e1) htc2)
          have hstep_e3 :=
            hIH_e3 hpredlaws1 (hframe'.skip hcanon1.within) hwfTm_ctxForE3 hTmBounded_ctxForE3 hfp_ctxForE3
              cfg₀1.memory cfg₁1.memory cfg₀1.varEnv cfg₁1.varEnv θ₀1 θ₁1
              cf₀ cf₁ o₀ o₁
              hθ₀1wf hθ₁1wf hwf_ctxForE3 htagBounded_ctxForE3 hric₀1_ctxForE3 hric₁1_ctxForE3 htagR_ctxForE3
              hcwr₀1_ctxForE3 hcwr₁1_ctxForE3
              (by simpa [ctxForE3, ctx'', ctx', pc', ctxAfter] using! hagree1)
              cfg₀1.nextAddr cfg₁1.nextAddr cfg₀1.pureMode hwfcf₀1'_e3m hwfcf₁1'
              hres₀1 hres₁1 hrdStdE3₀ hrdStdE3₁
              ht₀_e3'' ht₁_e3' hprem hroot₀3 hroot₁3
          rcases hstep_e3 with ⟨_tm3, _hcanon3, _hpredlaws3, _hresTm3, hstep_e3⟩
          rcases hstep_e3 with
            ⟨θ₀3, θ₁3, hθext₀3, hθext₁3, hvtyp₀3, hvtyp₁3, _hwfTm3, _hwf3, _htagBounded3, hwfcf₀3, hwfcf₁3,
              hric₀3, hric₁3, _htagR3, hcwr₀3, hcwr₁3, hagree3, hvalc₀3, hvalc₁3, hres_agree3, _hrd₀3s, _hrd₁3s,
              hM₀3, hM₁3, hF₀3, hF₁3⟩
          have hθext₀ : wfExtendsMap θ₀ θ₀3 := wfExtendsMap_trans hθext₀1 hθext₀3
          have hθext₁ : wfExtendsMap θ₁ θ₁3 := wfExtendsMap_trans hθext₁1 hθext₁3
          have hM₀_case : MapKeepsBelow ctxᵢ.nextLoc θ₀ θ₀3 := hM₀1.trans hM₀3 hnl_else
          have hM₁_case : MapKeepsBelow ctxᵢ.nextLoc θ₁ θ₁3 := hM₁1.trans hM₁3 hnl_else
          have hF₀_case : KeepsFootprints tm (ctxAfter ctxᵢ res).regime θ₀ μ₀ cf₀.memory :=
            KeepsFootprints.trans hF₀1 (KeepsFootprints.mono_regime hF₀3 hRright)
              hcanon1.extends_tm hθext₀1.1 hRback
          have hF₁_case : KeepsFootprints tm (ctxAfter ctxᵢ res).regime θ₁ μ₁ cf₁.memory :=
            KeepsFootprints.trans hF₁1 (KeepsFootprints.mono_regime hF₁3 hRright)
              hcanon1.extends_tm hθext₁1.1 hRback
          have hric₀3_ctx'' :
              runtimeInstantiatesCtx (ctxAfter ctx'' res3) cf₀.memory cf₀.varEnv θ₀3 := by
            simpa [ctxAfter, ctxForE3, ctx'', ctx', pc'] using hric₀3
          have hric₁3_ctx'' :
              runtimeInstantiatesCtx (ctxAfter ctx'' res3) cf₁.memory cf₁.varEnv θ₁3 := by
            simpa [ctxAfter, ctxForE3, ctx'', ctx', pc'] using hric₁3
          have hcwr₀3_ctx'' :
              consistentWithRegime predSat
                (ctxAfter ctx'' res3).regime
                (ctxAfter ctx'' res3)
                cf₀.memory cf₀.varEnv θ₀3 := by
            simpa [ctxAfter, ctxForE3, ctx'', ctx', pc'] using hcwr₀3
          have hcwr₁3_ctx'' :
              consistentWithRegime predSat
                (ctxAfter ctx'' res3).regime
                (ctxAfter ctx'' res3)
                cf₁.memory cf₁.varEnv θ₁3 := by
            simpa [ctxAfter, ctxForE3, ctx'', ctx', pc'] using hcwr₁3
          have hagree3_ctx'' :
              agreeOnClean predSat
                (ctxAfter ctx'' res3).regime
                (ctxAfter ctx'' res3)
                cf₀.memory cf₀.varEnv θ₀3 cf₁.memory cf₁.varEnv θ₁3 := by
            simpa [ctxAfter, ctxForE3, ctx'', ctx', pc'] using hagree3
          have hric₀_join :
              runtimeInstantiatesCtx (ctxAfter ctx'' resJoin) cf₀.memory cf₀.varEnv θ₀3 := by
            have hsrc_mem_to_join :
                ∀ l, res3.memEnv'.contains l → resJoin.memEnv'.contains l :=
              joinTypeResults_mem_contains_of_member
                (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                hjoin (by simp)
            constructor
            · intro l a hθ
              have hloc_src := hric₀3_ctx''.1 l a hθ
              rcases hloc_src with ⟨hcontains_src, hmem_contains⟩
              exact ⟨hsrc_mem_to_join l hcontains_src, hmem_contains⟩
            · intro x qt hlookup
              have hlookup_src :
                  (ctxAfter ctx'' res3).varEnv.lookup x = some qt := by
                simpa [ctxAfter] using hlookup
              rcases hric₀3_ctx''.2 hlookup_src with ⟨v, hlookup_v, hv_typ⟩
              exact ⟨v, hlookup_v, hv_typ⟩
          have hric₁_join :
              runtimeInstantiatesCtx (ctxAfter ctx'' resJoin) cf₁.memory cf₁.varEnv θ₁3 := by
            have hsrc_mem_to_join :
                ∀ l, res3.memEnv'.contains l → resJoin.memEnv'.contains l :=
              joinTypeResults_mem_contains_of_member
                (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                hjoin (by simp)
            constructor
            · intro l a hθ
              have hloc_src := hric₁3_ctx''.1 l a hθ
              rcases hloc_src with ⟨hcontains_src, hmem_contains⟩
              exact ⟨hsrc_mem_to_join l hcontains_src, hmem_contains⟩
            · intro x qt hlookup
              have hlookup_src :
                  (ctxAfter ctx'' res3).varEnv.lookup x = some qt := by
                simpa [ctxAfter] using hlookup
              rcases hric₁3_ctx''.2 hlookup_src with ⟨v, hlookup_v, hv_typ⟩
              exact ⟨v, hlookup_v, hv_typ⟩
          have hcwr₀_join :
              consistentWithRegime predSat
                (ctxAfter ctx'' resJoin).regime
                (ctxAfter ctx'' resJoin)
                cf₀.memory cf₀.varEnv θ₀3 := by
            exact
              consistentWithRegime_join_from_right
                predSat ctx'' res2 res3 resJoin
                cf₀.memory cf₀.varEnv θ₀3
                rfl rfl hcwr₀3_ctx''
          have hcwr₁_join :
              consistentWithRegime predSat
                (ctxAfter ctx'' resJoin).regime
                (ctxAfter ctx'' resJoin)
                cf₁.memory cf₁.varEnv θ₁3 := by
            exact
              consistentWithRegime_join_from_right
                predSat ctx'' res2 res3 resJoin
                cf₁.memory cf₁.varEnv θ₁3
                rfl rfl hcwr₁3_ctx''
          have h_clean_join_to_res3 :
              ∀ qt,
                qtypCleanUnder (ctxAfter ctx'' resJoin).regime qt →
                qtypCleanUnder (ctxAfter ctx'' res3).regime qt := by
            intro qt hclean
            cases hclean with
            | clean hpoison =>
                exact qtypCleanUnder.clean hpoison
            | guard k htag hk hnotfun =>
                have hk3 :
                    (ctxAfter ctx'' res3).regime.lookup? k = some true :=
                  joinTypeResults_lookup_member_regime_compat
                    (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                    hjoin (by simp) k true hk
                exact qtypCleanUnder.guard k htag hk3 hnotfun
          have h_mem_from_res3_or_unrealized :
              ∀ l qt,
                (ctxAfter ctx'' resJoin).memEnv.lookup l = some qt →
                qtypCleanUnder (ctxAfter ctx'' resJoin).regime qt →
                ((∃ qt3,
                    (ctxAfter ctx'' res3).memEnv.lookup l = some qt3 ∧
                    qtypCleanUnder (ctxAfter ctx'' res3).regime qt3 ∧
                    qt.etyp = qt3.etyp ∧
                    (qt.poison = false → qt3.poison = false)) ∨
                  (θ₀3.lookup l = none ∧ θ₁3.lookup l = none)) := by
            intro l qt hlookup hclean
            by_cases hlookup3_none : (ctxAfter ctx'' res3).memEnv.lookup l = none
            · right
              have hnot_contains3 : ¬ (ctxAfter ctx'' res3).memEnv.contains l := by
                intro hcontains
                have hmem : l ∈ (ctxAfter ctx'' res3).memEnv :=
                  (Std.ExtTreeMap.contains_iff_mem).1 hcontains
                have hlookup_isSome :
                    ((ctxAfter ctx'' res3).memEnv[l]?).isSome = true :=
                  (Std.ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
                have hlookup_get_none :
                    (ctxAfter ctx'' res3).memEnv[l]? = none := by
                  simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hlookup3_none
                simp [hlookup_get_none] at hlookup_isSome
              have hθ₀3_none :
                  θ₀3.lookup l = none :=
                theta_not_contains_if_not_in_memEnv
                  (ctx := (ctxAfter ctx'' res3))
                  (μ := cf₀.memory) (ρ := cf₀.varEnv) (θ := θ₀3)
                  (l := l) hric₀3_ctx'' hnot_contains3
              have hθ₁3_none :
                  θ₁3.lookup l = none :=
                theta_not_contains_if_not_in_memEnv
                  (ctx := (ctxAfter ctx'' res3))
                  (μ := cf₁.memory) (ρ := cf₁.varEnv) (θ := θ₁3)
                  (l := l) hric₁3_ctx'' hnot_contains3
              exact ⟨hθ₀3_none, hθ₁3_none⟩
            · left
              rcases Option.ne_none_iff_exists'.1 hlookup3_none with ⟨qt3, hlookup3⟩
              have hclean3 : qtypCleanUnder (ctxAfter ctx'' res3).regime qt3 :=
                joinTypeResults_lookup_member_clean_compat
                  (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                  hjoin (by simp) l qt qt3 hlookup hclean hlookup3
              have hetyp3 : qt.etyp = qt3.etyp :=
                joinTypeResults_lookup_member_etyp_compat
                  (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                  hjoin (by simp) l qt qt3 hlookup hlookup3
              have hpoison3 : qt.poison = false → qt3.poison = false :=
                joinTypeResults_lookup_member_poison_imp
                  (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                  hjoin (by simp) l qt qt3 hlookup hlookup3
              exact ⟨qt3, hlookup3, hclean3, hetyp3, hpoison3⟩
          have hlookup_back_join_to_res3 :
              ∀ k b,
                (ctxAfter ctx'' resJoin).regime.lookup? k = some b →
                (ctxAfter ctx'' res3).regime.lookup? k = some b := by
            intro k b hk
            exact
              joinTypeResults_lookup_member_regime_compat
                (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                hjoin (by simp) k b hk
          have hagree_join :
              agreeOnClean predSat
                (ctxAfter ctx'' resJoin).regime
                (ctxAfter ctx'' resJoin)
                cf₀.memory cf₀.varEnv θ₀3 cf₁.memory cf₁.varEnv θ₁3 := by
            exact
              ite_join_transport_agreeOnClean_from_member
                (predSat := predSat)
                (ctx := ctx'')
                (first := res2)
                (src := res3)
                (rest := [res3])
                (res := resJoin)
                (μ₀ := cf₀.memory) (μ₁ := cf₁.memory)
                (ρ₀ := cf₀.varEnv) (ρ₁ := cf₁.varEnv)
                (θ₀ := θ₀3) (θ₁ := θ₁3)
                hjoin (by simp) hagree3_ctx''
                h_clean_join_to_res3
                h_mem_from_res3_or_unrealized
                (fun {σcap} {ρcap} h =>
                  memberVarsRegimeEvidence_transport_lookup_back
                    (predSat := predSat)
                    (R := (ctxAfter ctx'' res3).regime)
                    (R' := (ctxAfter ctx'' resJoin).regime)
                    (μ := cf₀.memory)
                    hlookup_back_join_to_res3 h)
                (fun {σcap} {ρcap} h =>
                  memberCvcrEvidence_transport_lookup_back
                    (predSat := predSat)
                    (R := (ctxAfter ctx'' res3).regime)
                    (R' := (ctxAfter ctx'' resJoin).regime)
                    (μ := cf₀.memory)
                    hlookup_back_join_to_res3 h)
                (fun {σcap} {ρcap} h =>
                  memberVarsRegimeEvidence_transport_lookup_back
                    (predSat := predSat)
                    (R := (ctxAfter ctx'' res3).regime)
                    (R' := (ctxAfter ctx'' resJoin).regime)
                    (μ := cf₁.memory)
                    hlookup_back_join_to_res3 h)
                (fun {σcap} {ρcap} h =>
                  memberCvcrEvidence_transport_lookup_back
                    (predSat := predSat)
                    (R := (ctxAfter ctx'' res3).regime)
                    (R' := (ctxAfter ctx'' resJoin).regime)
                    (μ := cf₁.memory)
                    hlookup_back_join_to_res3 h)
          rcases typecheck_preserves_predSatLaws predSat tm ctxᵢ
              (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res
              hwfTm hTmBounded hframe htc with
            ⟨tmOut, hcanonOut, hpredlawsOut, hwithinOut⟩
          have hresTm : QTypRespectsTagMeaning tmOut res.qualType :=
            IsCanonicalExtension.respectsResult hcanonOut
          have hwfTm_final : wfTagMeaningCtx tmOut (ctxAfter ctxᵢ res) :=
            IsCanonicalExtension.wfCtx hcanonOut
          have hwf_final : wfTypeContext (ctxAfter ctxᵢ res) :=
            wfTypeContext_of_wfTypeResult ctxᵢ res
              (typecheckExpr_preserves_wfTypeResult
                ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res hwf htc)
              hwf (typecheck_nextLoc_mono ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res htc)
          have htagBounded_final : TagBoundedCtx (ctxAfter ctxᵢ res) :=
            typecheckExpr_preserves_TagBoundedCtx ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res (by simpa [typecheck] using htc) htagBounded
          have htag_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) :=
            typecheckExpr_preserves_regimeConsistentWithCtx
              ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res htagR htc
          have hvtyp₀_join : valueHasETyp θ₀3 o₀ resJoin.qualType.etyp := by
            exact
              joinTypeResults_transport_valueHasETyp_from_member
                (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                (θ := θ₀3) (v := o₀)
                hjoin (by simp) hvtyp₀3
          have hvtyp₁_join : valueHasETyp θ₁3 o₁ resJoin.qualType.etyp := by
            exact
              joinTypeResults_transport_valueHasETyp_from_member
                (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                (θ := θ₁3) (v := o₁)
                hjoin (by simp) hvtyp₁3
          have hvtyp₀_final : valueHasETyp θ₀3 o₀ res.qualType.etyp := by
            simpa [hresJoin_etyp] using hvtyp₀_join
          have hvtyp₁_final : valueHasETyp θ₁3 o₁ res.qualType.etyp := by
            simpa [hresJoin_etyp] using hvtyp₁_join
          have hric₀_final :
              runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀3 := by
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using! hric₀_join
          have hric₁_final :
              runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁3 := by
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using! hric₁_join
          have hcwr₀_final :
              consistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                (ctxAfter ctxᵢ res)
                cf₀.memory cf₀.varEnv θ₀3 := by
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using! hcwr₀_join
          have hcwr₁_final :
              consistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                (ctxAfter ctxᵢ res)
                cf₁.memory cf₁.varEnv θ₁3 := by
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using! hcwr₁_join
          have hagree_final :
              agreeOnClean predSat
                (ctxAfter ctxᵢ res).regime
                (ctxAfter ctxᵢ res)
                cf₀.memory cf₀.varEnv θ₀3 cf₁.memory cf₁.varEnv θ₁3 := by
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using! hagree_join
          have hvalc₀_join :
              valueConsistentWithRegime predSat
                (ctxAfter ctx'' resJoin).regime
                resJoin.qualType cf₀.memory θ₀3 o₀ := by
            exact
              joinTypeResults_transport_valueConsistentWithRegime_from_member
                (predSat := predSat)
                (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                (μ := cf₀.memory) (θ := θ₀3) (v := o₀)
                hjoin (by simp) (by simpa [ctxAfter, ctxForE3, ctx'', ctx', pc'] using hvalc₀3)
          have hvalc₁_join :
              valueConsistentWithRegime predSat
                (ctxAfter ctx'' resJoin).regime
                resJoin.qualType cf₁.memory θ₁3 o₁ := by
            exact
              joinTypeResults_transport_valueConsistentWithRegime_from_member
                (predSat := predSat)
                (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                (μ := cf₁.memory) (θ := θ₁3) (v := o₁)
                hjoin (by simp) (by simpa [ctxAfter, ctxForE3, ctx'', ctx', pc'] using hvalc₁3)
          have hvalc₀_final :
              valueConsistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                res.qualType cf₀.memory θ₀3 o₀ := by
            refine valueConsistentWithRegime.noTag ?_ ?_
            · simp [qtypGuardTag, hpredNo]
            · have hcap_join :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    resJoin.qualType cf₀.memory θ₀3 o₀ :=
                valueConsistentWithRegime_closureCapturedVarsRegime hvalc₀_join
              have hcap_res :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    res.qualType cf₀.memory θ₀3 o₀ :=
                closureCapturedVarsRegime_transport_etyp hresJoin_etyp hcap_join
              simpa [ctxAfter, ctx'', ctx', pc', resJoin, hregime'] using hcap_res
          have hvalc₁_final :
              valueConsistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                res.qualType cf₁.memory θ₁3 o₁ := by
            refine valueConsistentWithRegime.noTag ?_ ?_
            · simp [qtypGuardTag, hpredNo]
            · have hcap_join :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    resJoin.qualType cf₁.memory θ₁3 o₁ :=
                valueConsistentWithRegime_closureCapturedVarsRegime hvalc₁_join
              have hcap_res :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    res.qualType cf₁.memory θ₁3 o₁ :=
                closureCapturedVarsRegime_transport_etyp hresJoin_etyp hcap_join
              have hreg_final :
                  (ctxAfter ctx'' resJoin).regime = (ctxAfter ctxᵢ res).regime := by
                change joinRegimes res2.regime' res3.regime' = res.regime'
                exact hregime'.symm
              exact hreg_final ▸ hcap_res
          have hsrc_res3 : res3 ∈ res2 :: [res3] := by
            simp
          have hres_agree_join :
              resultAgreesIfClean predSat
                (ctxAfter ctx'' resJoin).regime
                cf₀.memory cf₁.memory θ₀3 θ₁3 resJoin.qualType o₀ o₁ := by
            exact
              joinTypeResults_transport_resultAgreesIfClean_from_member
                (predSat := predSat)
                (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                (μ₀ := cf₀.memory) (μ₁ := cf₁.memory)
                (θ₀ := θ₀3) (θ₁ := θ₁3)
                (o₀ := o₀) (o₁ := o₁)
                hjoin hsrc_res3 hres_agree3
          have hres_agree_final :
              resultAgreesIfClean predSat
                (ctxAfter ctxᵢ res).regime
                cf₀.memory cf₁.memory θ₀3 θ₁3 res.qualType o₀ o₁ := by
            have hreg_final :
                (ctxAfter ctx'' resJoin).regime = (ctxAfter ctxᵢ res).regime := by
              change joinRegimes res2.regime' res3.regime' = res.regime'
              exact hregime'.symm
            intro hclean
            have hclean_resJoin_reg :
                qtypCleanUnder (ctxAfter ctx'' resJoin).regime res.qualType := by
              exact hreg_final.symm ▸ hclean
            have hclean_join :
                qtypCleanUnder (ctxAfter ctx'' resJoin).regime resJoin.qualType := by
              cases hclean with
              | clean hpoison_res =>
                  exact qtypCleanUnder.clean (by simpa [hresJoin_poison] using hpoison_res)
              | guard k htag _hk _hnotfun =>
                  exfalso
                  simp [qtypGuardTag, hpredNo] at htag
            have hagree_join :
                agreeValueUnder predSat
                  (ctxAfter ctx'' resJoin).regime
                  cf₀.memory cf₁.memory θ₀3 θ₁3
                  resJoin.qualType o₀ o₁ :=
              hres_agree_join hclean_join
            have hpoison_imp :
                res.qualType.poison = false → resJoin.qualType.poison = false := by
              intro hpoison_res
              simpa [hresJoin_poison] using hpoison_res
            have hagree_res :
                agreeValueUnder predSat
                  (ctxAfter ctx'' resJoin).regime
                  cf₀.memory cf₁.memory θ₀3 θ₁3
                  res.qualType o₀ o₁ :=
              agreeValueUnder_transport_clean
                (predSat := predSat)
                (R := (ctxAfter ctx'' resJoin).regime)
                (μ₀ := cf₀.memory) (μ₁ := cf₁.memory)
                (θ₀ := θ₀3) (θ₁ := θ₁3)
                (qt := res.qualType) (qt2 := resJoin.qualType)
                (o₀ := o₀) (o₁ := o₁)
                hclean_resJoin_reg hresJoin_etyp.symm hpoison_imp hagree_join
            exact hreg_final ▸ hagree_res
          exact
            ⟨tmOut, BoundaryTagMeaningPost.of_isCanonical_predSat hcanonOut hpredlawsOut hwithinOut,
              hpredlawsOut, hresTm, θ₀3, θ₁3, hθext₀, hθext₁, hvtyp₀_final, hvtyp₁_final,
              hwfTm_final, hwf_final, htagBounded_final, hwfcf₀3, hwfcf₁3,
              hric₀_final, hric₁_final, htag_final,
              hcwr₀_final, hcwr₁_final, hagree_final,
              hvalc₀_final, hvalc₁_final, hres_agree_final,
              (by rw [hdecl']; exact _hrd₀3s),
              (by rw [hdecl']; exact _hrd₁3s),
              hM₀_case, hM₁_case, hF₀_case, hF₁_case⟩

-- Main lemma that dispatches to mode-specific lemmas
lemma stepFR_ite_with_expr_proof
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 e3 : Expr) (fuel' : Nat) (res : TypeResult)
  (CanUse : Expr → Prop) (CtxReach : TypeContext → Prop)
  (hOp : RegistryOperationalSafe registry)
  (hctxCurrent : CtxReach ctxᵢ)
  (hctxPure : CtxReach { ctxᵢ with pureCtx := true })
  (hctxTagTrue :
    ∀ k deps (nextTag : Nat) (declared : List ExternId),
      CtxReach { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩,
                           nextTag := nextTag,
                           declaredExternRefs := declared })
  (hctxTagFalse :
    ∀ k deps nextLoc nextTag (declared : List ExternId),
      CtxReach
        { ctxᵢ with
          tagEnv := ctxᵢ.tagEnv.insert k ⟨false, deps⟩,
          nextLoc := nextLoc,
          nextTag := nextTag,
          declaredExternRefs := declared })
  (hctxStandardThen :
    ∀ {res1 : TypeResult},
      typecheck ctxᵢ e1 fuel' = .ok res1 →
        CtxReach
          { { ctxᵢ with
              memEnv := res1.memEnv',
              tagEnv := res1.tagEnv',
              nextLoc := res1.nextLoc',
              nextTag := res1.nextTag',
              regime := res1.regime',
              declaredExternRefs := res1.declared' } with
            pc := joinPoison ctxᵢ.pc res1.qualType.poison })
  (hctxStandardElse :
    ∀ {res1 res2 : TypeResult},
      typecheck ctxᵢ e1 fuel' = .ok res1 →
        CtxReach
          { { { ctxᵢ with
                memEnv := res1.memEnv',
                tagEnv := res1.tagEnv',
                nextLoc := res1.nextLoc',
                nextTag := res1.nextTag',
                regime := res1.regime',
                declaredExternRefs := res1.declared' } with
              pc := joinPoison ctxᵢ.pc res1.qualType.poison } with
            nextLoc := res2.nextLoc',
            nextTag := res2.nextTag',
            declaredExternRefs := res2.declared' })
  (hcan1 : CanUse e1) (hcan2 : CanUse e2) (hcan3 : CanUse e3)
  (IH :
    StepFR_IH_WithExprCtx predSat tm (Nat.succ (Nat.succ fuel'))
      CanUse CtxReach (registry := registry))
  (singleIH :
    StepFRSingleRunFinalCleanPcTrue_IH_WithExprCtx
      predSat tm (Nat.succ (Nat.succ fuel')) CanUse CtxReach (registry := registry))
  (hkeepFP : TypingKeepsFootprintCtx)
  (htc : typecheck ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR ctxᵢ (Expr.ite e1 e2 e3) res predSat tm (Nat.succ (Nat.succ fuel')) (registry := registry) := by
  classical
  -- Parse typecheck result
  have htc' : typecheckIf ctxᵢ e1 e2 e3 (Nat.succ fuel') = .ok res := by
    simpa [typecheck, typecheckExpr] using htc
  have hstruct := typecheckIf_structure ctxᵢ e1 e2 e3 (Nat.succ fuel') res htc'
  -- Case split on typecheck structure (known true / known false / standard)
  cases hstruct with
  | inl h_true =>
    -- Known true case: the then-branch is the only proof-relevant path.
    obtain ⟨k, deps, hmatch, hregime_true, res1, htc1, hbool, res2, _res3, htc2, _htc3,
            hmemEnv, htagEnv, hnextLoc_max, hnextTag_max, hregime', _hdecl', hpoison, hetyp⟩ := h_true
    exact stepFR_ite_true ctxᵢ predSat tm e1 e2 e3 fuel' res
      CanUse CtxReach hOp hctxPure hcan1 hcan2 IH htc k deps hmatch hregime_true
      res1 res2 htc1 hbool htc2 (hctxTagTrue k deps res1.nextTag' res1.declared') _res3 _htc3 hmemEnv htagEnv
      hnextLoc_max hnextTag_max hregime' _hdecl'
      hpoison hetyp
      (typecheckIf_tagLog_matched htc' hmatch hregime_true htc1 htc2 _htc3)
  | inr h_rest =>
    cases h_rest with
    | inl h_false =>
      -- Known false case: the else-branch is the only proof-relevant path.
      obtain ⟨k, deps, hmatch, hregime_false, res1, htc1, hbool, _res2, res3, _htc2, htc3,
              hmemEnv, htagEnv, hnextLoc_max, hnextTag_max, hregime', _hdecl', hpoison, hetyp⟩ := h_false
      exact stepFR_ite_false ctxᵢ predSat tm e1 e2 e3 fuel' res
        CanUse CtxReach hOp hctxPure hcan1 hcan3 IH htc k deps hmatch hregime_false
        res1 htc1 hbool _res2 _htc2 res3 htc3
        (hctxTagFalse k deps _res2.nextLoc' _res2.nextTag' _res2.declared') hmemEnv htagEnv
        hnextLoc_max hnextTag_max hregime' _hdecl'
        hpoison hetyp
        (typecheckIf_tagLog_matched htc' hmatch hregime_false htc1 _htc2 htc3)
    | inr h_std =>
      obtain ⟨h_std_case, res1, htc1, hbool, res2, htc2, res3, htc3,
              hmemEnv, htagEnv, hnextLoc, hnextTag, hregime', _hdecl', hpoison, hetyp, hpred⟩ := h_std
      have hcompat_std :
          beqETypSignature res2.qualType.etyp res3.qualType.etyp = true :=
        typecheckIf_standard_compat_from_existing_hyps
          ctxᵢ e1 e2 e3 fuel' res res1 res2 res3
          h_std_case htc1 hbool htc2 htc3 htc'
      have htc1_tc : typecheck ctxᵢ e1 fuel' = .ok res1 := by
        simpa [typecheck, Nat.succ_sub_one] using htc1
      exact stepFR_ite_standard ctxᵢ predSat tm e1 e2 e3 fuel' res
        CanUse CtxReach hOp hctxCurrent hcan1 hcan2 hcan3 IH singleIH hkeepFP htc
        res1 res2 res3 htc1 hbool htc2 htc3 (hctxStandardThen htc1_tc)
        (hctxStandardElse htc1_tc) hmemEnv htagEnv hnextLoc hnextTag hregime' _hdecl' hpoison
        hcompat_std hetyp hpred
        (typecheckIf_tagLog_std htc' h_std_case htc1 htc2 htc3)
        (by simpa [StdArm] using h_std_case.symm)

/-- Masked single-run fault-robustness, `ite` case.

Used by the masked single-run theorem in `FaultRobustnessProofs`. `CanUse`,
`CtxReach`, the `CtxReach` navigation contracts, and the strong-induction
hypothesis `IH'` are explicit parameters; the three `CanUse` sub-expression
facts (`hcan1`/`hcan2`/`hcan3`) are supplied directly by the caller, mirroring
the `op`/`seq` arms. -/
lemma stepFRSingleRunFinalCleanPcTrue_ite_maskedReg_with_expr_proof
    (masked : Tag → Prop)
    (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
    (e1 e2 e3 : Expr) (fuel' : Nat) (res : TypeResult)
    (CanUse : Expr → Prop) (CtxReach : TypeContext → Prop)
    (hOp : RegistryOperationalSafe registry)
    (hcan1 : CanUse e1) (hcan2 : CanUse e2) (hcan3 : CanUse e3)
    (hctxCurrent : CtxReach ctxᵢ)
  (hctxPure :
    ∀ {ctx : TypeContext}, CtxReach ctx → CtxReach { ctx with pureCtx := true })
  (hctxTagTrue :
    ∀ {ctx : TypeContext} {k : Tag} {deps : Deps} {nextTag : Nat} {declared : List ExternId},
      CtxReach ctx →
        CtxReach { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩,
                            nextTag := nextTag,
                            declaredExternRefs := declared })
  (hctxTagFalseNext :
    ∀ {ctx : TypeContext} {k : Tag} {deps : Deps} {nextLoc nextTag : Nat}
      {declared : List ExternId},
      CtxReach ctx →
        CtxReach
          { ctx with
            tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩,
            nextLoc := nextLoc,
            nextTag := nextTag,
            declaredExternRefs := declared })
  (hctxAfterPc :
    ∀ {ctx : TypeContext} {res : TypeResult} {pc : Poison},
      CtxReach ctx → CtxReach { ctxAfter ctx res with pc := pc })
  (hctxNext :
    ∀ {ctx : TypeContext} {nextLoc nextTag : Nat} {declared : List ExternId},
      CtxReach ctx → CtxReach { ctx with nextLoc := nextLoc, nextTag := nextTag,
                                         declaredExternRefs := declared })
    (IH' :
          ∀ m < Nat.succ (Nat.succ fuel'), ∀ (tm' : TagMeaning) (masked' : Tag → Prop) (e' : Expr)
            (ctx' : TypeContext),
            CtxReach ctx' →
            CanUse e' →
            ∀ (res' : TypeResult),
            typecheck ctx' e' m = .ok res' →
            StepFRSingleRunFinalCleanPcTrueMaskedRegParam
              masked'
              (fun ctx μ ρ θ =>
                consistentWithRegimeMasked masked' predSat ctx.regime ctx μ ρ θ)
              (fun R qt μ θ v =>
                valueConsistentWithRegimeMasked masked' predSat R qt μ θ v)
              ctx' e' res' predSat tm' m (registry := registry))
    (hkeepFP : TypingKeepsFootprintCtx)
    (htc : typecheck ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) = .ok res) :
    StepFRSingleRunFinalCleanPcTrueMaskedRegParam
      masked
      (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
      (fun R qt μ θ v => valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
      ctxᵢ (Expr.ite e1 e2 e3) res predSat tm (Nat.succ (Nat.succ fuel')) (registry := registry) := by
                  unfold StepFRSingleRunFinalCleanPcTrueMaskedRegParam
                  have htcIf : typecheckIf ctxᵢ e1 e2 e3 (Nat.succ fuel') = .ok res := by
                    simpa [typecheck, typecheckExpr_ite_succ] using htc
                  have hstruct := typecheckIf_structure ctxᵢ e1 e2 e3 (Nat.succ fuel') res htcIf
                  rcases hstruct with h1 | h2 | hstd
                  · rcases h1 with
                      ⟨k, deps, hmatch, hregime_true, res1, htc1, hbool, res2, _res3, htc2, _htc3,
                        hmemEnv, htagEnv, hnextLoc_max, hnextTag_max, hregime', hdecl', _hpoison, hetyp⟩
                    have hlogArm := typecheckIf_tagLog_matched htcIf hmatch hregime_true htc1 htc2 _htc3
                    intro hpredlaws hframe hwfTm hTmBounded hfp
                    have hframe' := hframe.of_log_eq hlogArm
                    refine ⟨?_, ?_⟩
                    · exact
                        StepFRSingleRunTagMeaningPost.of_typecheck_preserves
                          predSat tm ctxᵢ (Expr.ite e1 e2 e3)
                          (Nat.succ (Nat.succ fuel')) res
                          hwfTm hTmBounded hframe htc
                    intro μ ρ θ cf o hθwf hwf hric htagR hmasked_none hmasked_absent hmasked_bounded hbnd hcwr a pm hwfcfg hres hrd ht hpc P hP hroot
                    let ctxPure : TypeContext := { ctxᵢ with pureCtx := true }
                    let ctxTrue : TypeContext := { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩,
                                                             nextTag := res1.nextTag',
                                                             declaredExternRefs := res1.declared' }
                    have htc1' : typecheck ctxPure e1 fuel' = .ok res1 := by
                      simpa [ctxPure, typecheck, Nat.succ_sub_one] using htc1
                    have hwfTm_pure : wfTagMeaningCtx tm ctxPure := by
                      simpa [ctxPure, wfTagMeaningCtx] using hwfTm
                    have hTmBounded_pure : TagMeaningBounded tm ctxPure.nextTag := by
                      simpa [ctxPure] using hTmBounded
                    have hwf_pure : wfTypeContext ctxPure := by
                      simpa [ctxPure, wfTypeContext] using hwf
                    have htagR_pure : regimeConsistentWithCtxMasked masked ctxPure := by
                      simpa [ctxPure, regimeConsistentWithCtxMasked] using htagR
                    have hmasked_none_pure :
                        ∀ t, masked t → ctxPure.regime.lookup? t = none := by
                      simpa [ctxPure] using hmasked_none
                    have hmasked_absent_pure :
                        MaskedTagsAbsentFromTrueTagEnv masked ctxPure := by
                      simpa [ctxPure, MaskedTagsAbsentFromTrueTagEnv] using hmasked_absent
                    have hmasked_bounded_pure :
                        ∀ t, masked t → t < ctxPure.nextTag := by
                      simpa [ctxPure] using hmasked_bounded
                    have hbnd_pure : TagBoundedCtx ctxPure := by
                      simpa [ctxPure] using! hbnd
                    have hcwr_pure :
                        consistentWithRegimeMasked masked predSat ctxPure.regime ctxPure μ ρ θ := by
                      simpa [ctxPure, consistentWithRegimeMasked] using hcwr
                    have hpc_pure : ctxPure.pc = true := by
                      simpa [ctxPure] using hpc
                    have hfp_pure : FootprintCtx tm ctxPure := hfp
                    have hIH_e1 := IH' fuel' (by omega) tm masked e1 ctxPure
                      (by simpa [ctxPure] using hctxPure hctxCurrent)
                      hcan1 res1 htc1'
                    have hstruct_rt := terminatesTo_ite_inv' e1 e2 e3
                      { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm,
                        registry := registry } cf o ht
                    rcases hstruct_rt with ⟨cfg1, b, ht_e1, hbranch, _hpm1, _hpmf⟩
                    rcases
                        (hIH_e1 hpredlaws hframe'.left.left hwfTm_pure hTmBounded_pure hfp_pure).2
                          μ ρ θ cfg1 (Value.bool b)
                          hθwf hwf_pure hric htagR_pure hmasked_none_pure
                          hmasked_absent_pure hmasked_bounded_pure hbnd_pure hcwr_pure
                          a pm hwfcfg hres hrd ht_e1 hpc_pure
                          hP (hP.closed hroot (SubStep.iteCondPure (f := fuel') hmatch hregime_true))
                      with ⟨θ1, hθext1, _hv1, hric1, hcwr1, _hvalc1, hpres1, _hfresh1, _hrd1, hM1, hF1⟩
                    have hcwr_unmasked :
                        consistentWithRegime predSat ctxᵢ.regime ctxᵢ μ ρ θ :=
                      consistentWithRegimeMasked_unmask
                        (masked := masked) (predSat := predSat)
                        (R := ctxᵢ.regime) (ctx := ctxᵢ)
                        (μ := μ) (ρ := ρ) (θ := θ)
                        hmasked_none hcwr
                    have hb_true : b = true := by
                      exact
                        matchGuard_runtime_branch_alignment
                          predSat tm
                          ctxᵢ μ ρ θ a pm
                          hwfTm hpredlaws hric hcwr_unmasked
                          e1 k deps true b cfg1
                          hmatch hregime_true ht_e1
                    have ht_e2 : terminatesTo e2 cfg1 cf o := by
                      cases hbranch with
                      | inl h => exact h.2
                      | inr h =>
                          have : false = true := by rw [← h.1, hb_true]
                          contradiction
                    have hθ1wf : wfRealizationMap θ1 := hθext1.2 hθwf
                    have hwfcfg1 : wfConfig cfg1 :=
                      (wfConfig_preserved e1 _ cfg1 (Value.bool b) hOp hres.toBelow ht_e1 hwfcfg).1
                    have htc2' : typecheck ctxTrue e2 fuel' = .ok res2 := by
                      simpa [ctxTrue, typecheck, Nat.succ_sub_one] using htc2
                    have hwfTm_true : wfTagMeaningCtx tm ctxTrue := by
                      simpa [ctxTrue, wfTagMeaningCtx] using hwfTm
                    have hb1 : ctxᵢ.nextTag ≤ res1.nextTag' :=
                      typecheck_nextTag_mono { ctxᵢ with pureCtx := true } e1 fuel' res1 htc1
                    have hTmBounded_true : TagMeaningBounded tm ctxTrue.nextTag :=
                      hTmBounded.mono hb1
                    have hfp_true : FootprintCtx tm ctxTrue :=
                      ⟨RecordsCover.matched (b := true) hwfTm hfp.1 hmatch, hfp.2⟩
                    have hwf_true : wfTypeContext ctxTrue := by
                      simpa [ctxTrue, wfTypeContext] using hwf
                    have htagR_true : regimeConsistentWithCtxMasked masked ctxTrue := by
                      exact
                        tagEnvConsistentWithRegimeMasked_insert_true
                          masked ctxᵢ.tagEnv ctxᵢ.regime k deps htagR hregime_true
                    have hmasked_none_true :
                        ∀ t, masked t → ctxTrue.regime.lookup? t = none := by
                      simpa [ctxTrue] using hmasked_none
                    have hmasked_absent_true :
                        MaskedTagsAbsentFromTrueTagEnv masked ctxTrue := by
                      have hnotMasked : masked k → False := by
                        intro hk
                        have hnone := hmasked_none k hk
                        rw [hregime_true] at hnone
                        contradiction
                      exact
                        MaskedTagsAbsentFromTrueTagEnv_insert_true
                          (masked := masked) (ctx := ctxᵢ) hmasked_absent hnotMasked
                    have hmasked_bounded_true :
                        ∀ t, masked t → t < ctxTrue.nextTag :=
                      fun t ht => Nat.lt_of_lt_of_le (hmasked_bounded t ht) hb1
                    have hbnd_true : TagBoundedCtx ctxTrue := by
                      obtain ⟨hb_tag, ⟨hb_predV, hb_predM⟩, hb_clos⟩ := hbnd
                      have hk_lt := matchGuard_tag_bounded e1 ctxᵢ.memEnv ctxᵢ.varEnv fuel'
                        k deps ctxᵢ.nextTag hmatch hb_predV hb_predM
                      exact ⟨tagEnvBounded_mono _ _ _
                          (tagEnvBounded_insert_of_lt ctxᵢ.tagEnv ctxᵢ.nextTag k _ hb_tag hk_lt) hb1,
                        ⟨predTagsBoundedInVarEnv_mono hb_predV hb1, predTagsBoundedInMemEnv_mono hb_predM hb1⟩,
                        varEnvClosuresCapturedBounded_mono hb_clos hb1⟩
                    rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
                    have hric1' : runtimeInstantiatesCtx ctxTrue cfg1.memory cfg1.varEnv θ1 := by
                      have hsub : ∀ l, res1.memEnv'.contains l → ctxᵢ.memEnv.contains l := by
                        exact
                          typecheckExpr_pure_mem_subset_of_toPExpr
                            (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
                            hpe1 htc1
                      exact
                        runtimeInstantiatesCtx_transport_mem_subset_tag_insert_true
                          (ctx := ctxᵢ) (res := res1) (μ := cfg1.memory) (ρ := cfg1.varEnv) (θ := θ1)
                          (k := k) (deps := deps)
                          hsub hric1
                    have hcwr1' :
                        consistentWithRegimeMasked masked predSat ctxTrue.regime ctxTrue
                          cfg1.memory cfg1.varEnv θ1 := by
                      refine
                        consistentWithRegimeMasked_transport_ctxAfter_pure_to_ctx_insert_true
                          masked predSat ctxᵢ res1
                          cfg1.memory cfg1.varEnv θ1
                          k deps
                          ?_ ?_ hcwr1
                      · intro k' b' hk
                        exact
                          typecheckExpr_pure_regime_bridge_of_toPExpr
                            (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
                            hpe1 htc1 k' b' hk
                      · intro l qt k' hlookup hguard hRdef
                        exact
                          typecheckExpr_pure_guarded_mem_bridge_of_toPExpr
                            (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
                            hpe1 htc1 l qt k' hlookup hguard hRdef
                    have hpc_true : ctxTrue.pc = true := by
                      simpa [ctxTrue] using hpc
                    have hpredNo : res.qualType.pred = Predicate.noPred := by
                      exact typecheckIf_pred_noPred ctxᵢ e1 e2 e3 (Nat.succ fuel') res htcIf
                    have hIH_e2 := IH' fuel' (by omega) tm masked e2 ctxTrue
                      (by simpa [ctxTrue] using hctxTagTrue hctxCurrent)
                      hcan2 res2 htc2'
                    -- Thread extern registry.
                    have hreg_cfg1_t : cfg1.registry = registry := by
                      simpa using terminatesTo_preserves_registry ht_e1
                    have hcfg1_eq_t : cfg1 = { memory := cfg1.memory, varEnv := cfg1.varEnv, nextAddr := cfg1.nextAddr, pureMode := cfg1.pureMode, registry := registry } :=
                      config_eq_of_registry cfg1 registry hreg_cfg1_t
                    have hwfcfg1_t : wfConfig { memory := cfg1.memory, varEnv := cfg1.varEnv, nextAddr := cfg1.nextAddr, pureMode := cfg1.pureMode, registry := registry } := by
                      rw [← hcfg1_eq_t]; exact hwfcfg1
                    have ht_e2_t : terminatesTo e2 { memory := cfg1.memory, varEnv := cfg1.varEnv, nextAddr := cfg1.nextAddr, pureMode := cfg1.pureMode, registry := registry } cf o := by
                      rw [← hcfg1_eq_t]; exact ht_e2
                    have hres_cfg1 : RegistryReservedWF registry cfg1.memory cfg1.nextAddr := by
                      apply RegistryReservedWF_mono hres
                      · exact terminatesTo_memory_contains_mono e1
                          { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry }
                          cfg1 (Value.bool b) hOp ht_e1
                      · exact terminatesTo_nextAddr_mono e1
                          { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry }
                          cfg1 (Value.bool b) hOp ht_e1
                    have hrd_true : ReservedDiscipline registry ctxTrue.declaredExternRefs θ1 := by
                      simp only [ctxTrue]
                      simpa [hreg_cfg1_t] using _hrd1
                    have hroot2t : P ⟨ctxTrue, e2, fuel',
                        { memory := cfg1.memory, varEnv := cfg1.varEnv, nextAddr := cfg1.nextAddr, pureMode := cfg1.pureMode, registry := registry }⟩ := by
                      rw [← hcfg1_eq_t]
                      exact hP.closed hroot (SubStep.iteThenMatched (f := fuel') hmatch hregime_true htc1
                        (by simpa [hb_true] using ht_e1))
                    rcases
                        (hIH_e2 hpredlaws hframe'.left.right hwfTm_true hTmBounded_true hfp_true).2
                          cfg1.memory cfg1.varEnv θ1 cf o
                          hθ1wf hwf_true hric1' htagR_true hmasked_none_true
                          hmasked_absent_true hmasked_bounded_true hbnd_true hcwr1'
                          cfg1.nextAddr cfg1.pureMode hwfcfg1_t hres_cfg1 hrd_true
                          ht_e2_t hpc_true hP hroot2t
                      with ⟨θ2, hθext2, hv2, hric2, hcwr2, hvalc2, hpres2, _hfresh2, _hrd2, hM2, hF2⟩
                    have hθext : wfExtendsMap θ θ2 := wfExtendsMap_trans hθext1 hθext2
                    have hctxAfter_memEnv : (ctxAfter ctxᵢ res).memEnv = (ctxAfter ctxTrue res2).memEnv := by
                      simp [ctxAfter, hmemEnv]
                    have hctxAfter_varEnv : (ctxAfter ctxᵢ res).varEnv = (ctxAfter ctxTrue res2).varEnv := by
                      simp [ctxAfter, ctxTrue]
                    have hctxAfter_regime : (ctxAfter ctxᵢ res).regime = (ctxAfter ctxTrue res2).regime := by
                      simp [ctxAfter, hregime']
                    -- Footprint bookkeeping: compose the condition run and the then-branch run.
                    have hRback : ∀ k' d, tm.lookup k' = some d →
                        (ctxAfter ctxTrue res2).regime.lookup? k' ≠ none →
                        (ctxAfter ctxPure res1).regime.lookup? k' ≠ none := by
                      intro k' d hd hk'
                      have h := regime_defined_back (regime_monotoneExt ctxTrue e2 fuel' res2 htc2')
                        hTmBounded_true k' d hd (by simpa [ctxAfter] using hk')
                      cases hl : ctxTrue.regime.lookup? k' with
                      | none => exact absurd hl h
                      | some b' =>
                          have hb := typecheckExpr_pure_regime_bridge_of_toPExpr
                            (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
                            hpe1 htc1 k' b' (by simpa [ctxTrue] using hl)
                          simp [ctxAfter, ctxPure, hb]
                    have hM_case : MapKeepsBelow ctxᵢ.nextLoc θ θ2 := hM1.trans hM2 (Nat.le_refl _)
                    have hF_case : KeepsFootprints tm (ctxAfter ctxᵢ res).regime θ μ cf.memory := by
                      rw [hctxAfter_regime]
                      exact KeepsFootprints.trans hF1 hF2 (TagMeaningExtends.refl tm) hθext1.1 hRback
                    have hpres_final :
                        PreservesInheritedFinalCleanLocsOneRun ctxᵢ res μ cf.memory θ θ2 := by
                      refine ⟨?_⟩
                      intro l qt_in qt_out hlookup_in hlookup_out hclean_out
                      rcases
                          typecheckExpr_clean_lookup_origin_of_pc_true
                            ctxTrue e2 fuel' res2 htc2 hwf_true hbnd_true hpc_true
                            l qt_out (by simpa [hmemEnv] using hlookup_out)
                            (by simpa [ctxTrue] using memEnv_contains_of_lookup_some ctxᵢ.memEnv l qt_in hlookup_in)
                            (by simpa [hregime'] using hclean_out)
                        with ⟨qt_mid, hlookup_mid_true, hclean_mid_true⟩
                      have hlookup_mid_res1 : res1.memEnv'.lookup l = some qt_mid := by
                        exact
                          typecheckExpr_pure_mem_lookup_bridge_of_toPExpr
                            (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
                            hpe1 htc1 l qt_mid (by simpa [ctxTrue] using hlookup_mid_true)
                      have hclean_mid_res1 : qtypCleanUnder res1.regime' qt_mid := by
                        exact
                          qtypCleanUnder_transport_pure_regime_of_toPExpr
                            ctxᵢ e1 pe1 fuel' res1 hpe1 htc1 qt_mid
                            (by simpa [ctxTrue] using hclean_mid_true)
                      have hpres_mid :
                          PreservesInheritedCleanLocOneRun μ cfg1.memory θ θ1 l :=
                        PreservesInheritedFinalCleanLocsOneRun.apply
                          (ctx := ctxPure) (res := res1)
                          (μ_in := μ) (μ_out := cfg1.memory) (θ_in := θ) (θ_out := θ1)
                          hpres1
                          (by simpa [ctxPure] using hlookup_in)
                          hlookup_mid_res1
                          hclean_mid_res1
                      have hpres_last :
                          PreservesInheritedCleanLocOneRun cfg1.memory cf.memory θ1 θ2 l :=
                        PreservesInheritedFinalCleanLocsOneRun.apply
                          (ctx := ctxTrue) (res := res2)
                          (μ_in := cfg1.memory) (μ_out := cf.memory) (θ_in := θ1) (θ_out := θ2)
                          hpres2
                          hlookup_mid_true
                          (by simpa [hmemEnv] using hlookup_out)
                          (by simpa [hregime'] using hclean_out)
                      exact PreservesInheritedCleanLocOneRun.trans hpres_mid hpres_last
                    have hfresh_final : FreshCleanLocsUnrealizedOneRun ctxᵢ res θ2 := by
                      intro l qt hnotIn hlookup hclean
                      exact _hfresh2 l qt (by simpa [ctxTrue] using hnotIn)
                        (by simpa [hmemEnv] using hlookup) (by simpa [hregime'] using hclean)
                    refine ⟨θ2, hθext, ?_, ?_, ?_, ?_, hpres_final, hfresh_final, ?_, hM_case, hF_case⟩
                    · simpa [hetyp] using hv2
                    · simp only [runtimeInstantiatesCtx, hctxAfter_memEnv, hctxAfter_varEnv]
                      exact hric2
                    · simp only [consistentWithRegimeMasked, hctxAfter_regime,
                        hctxAfter_memEnv, hctxAfter_varEnv]
                      exact hcwr2
                    · refine valueConsistentWithRegimeMasked.noTag ?_ ?_
                      · simp [qtypGuardTag, hpredNo]
                      ·
                        have hcap2 :
                            closureCapturedVarsRegimeMasked masked predSat
                              (ctxAfter ctxTrue res2).regime
                              res2.qualType cf.memory θ2 o :=
                          valueConsistentWithRegimeMasked_closureCapturedVarsRegime hvalc2
                        have hcap2' :
                            closureCapturedVarsRegimeMasked masked predSat
                              (ctxAfter ctxᵢ res).regime
                              res2.qualType cf.memory θ2 o := by
                          rwa [hctxAfter_regime]
                        exact
                          closureCapturedVarsRegimeMasked_transport_etyp
                            (qt := res2.qualType) (qt' := res.qualType)
                            hetyp.symm hcap2'
                    · -- ReservedDiscipline: e3's (unexecuted) typechecking only grows the set
                      rw [hdecl']
                      exact ReservedDiscipline.mono_declared
                        (fun id h => typecheck_declared'_mono _ e3 fuel' _res3
                          (by simpa [typecheck] using _htc3) id h)
                        _hrd2
                  · rcases h2 with
                      ⟨k, deps, hmatch, hregime_false, res1, htc1, hbool, _res2, res3, _htc2, htc3,
                        hmemEnv, htagEnv, hnextLoc_max, hnextTag_max, hregime', hdecl', _hpoison, hetyp⟩
                    have hlogArm := typecheckIf_tagLog_matched htcIf hmatch hregime_false htc1 _htc2 htc3
                    intro hpredlaws hframe hwfTm hTmBounded hfp
                    have hframe' := hframe.of_log_eq hlogArm
                    refine ⟨?_, ?_⟩
                    · exact
                        StepFRSingleRunTagMeaningPost.of_typecheck_preserves
                          predSat tm ctxᵢ (Expr.ite e1 e2 e3)
                          (Nat.succ (Nat.succ fuel')) res
                          hwfTm hTmBounded hframe htc
                    intro μ ρ θ cf o hθwf hwf hric htagR hmasked_none hmasked_absent hmasked_bounded hbnd hcwr a pm hwfcfg hres hrd ht hpc P hP hroot
                    let ctxPure : TypeContext := { ctxᵢ with pureCtx := true }
                    let ctxFalse : TypeContext := { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨false, deps⟩,
                                                              declaredExternRefs := res1.declared' }
                    let ctxFalse' : TypeContext :=
                      { ctxFalse with nextLoc := _res2.nextLoc', nextTag := _res2.nextTag',
                                      declaredExternRefs := _res2.declared' }
                    have htc1' : typecheck ctxPure e1 fuel' = .ok res1 := by
                      simpa [ctxPure, typecheck, Nat.succ_sub_one] using htc1
                    have hwfTm_pure : wfTagMeaningCtx tm ctxPure := by
                      simpa [ctxPure, wfTagMeaningCtx] using hwfTm
                    have hTmBounded_pure : TagMeaningBounded tm ctxPure.nextTag := by
                      simpa [ctxPure] using hTmBounded
                    have hwf_pure : wfTypeContext ctxPure := by
                      simpa [ctxPure, wfTypeContext] using hwf
                    have htagR_pure : regimeConsistentWithCtxMasked masked ctxPure := by
                      simpa [ctxPure, regimeConsistentWithCtxMasked] using htagR
                    have hmasked_none_pure :
                        ∀ t, masked t → ctxPure.regime.lookup? t = none := by
                      simpa [ctxPure] using hmasked_none
                    have hmasked_absent_pure :
                        MaskedTagsAbsentFromTrueTagEnv masked ctxPure := by
                      simpa [ctxPure, MaskedTagsAbsentFromTrueTagEnv] using hmasked_absent
                    have hmasked_bounded_pure :
                        ∀ t, masked t → t < ctxPure.nextTag := by
                      simpa [ctxPure] using hmasked_bounded
                    have hbnd_pure : TagBoundedCtx ctxPure := by
                      simpa [ctxPure] using! hbnd
                    have hcwr_pure :
                        consistentWithRegimeMasked masked predSat ctxPure.regime ctxPure μ ρ θ := by
                      simpa [ctxPure, consistentWithRegimeMasked] using hcwr
                    have hpc_false : ctxFalse.pc = true := by
                      simpa [ctxFalse] using hpc
                    have hfp_pure : FootprintCtx tm ctxPure := hfp
                    have hIH_e1 := IH' fuel' (by omega) tm masked e1 ctxPure
                      (by simpa [ctxPure] using hctxPure hctxCurrent)
                      hcan1 res1 htc1'
                    have hstruct_rt := terminatesTo_ite_inv' e1 e2 e3
                      { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm,
                        registry := registry } cf o ht
                    rcases hstruct_rt with ⟨cfg1, b, ht_e1, hbranch, _hpm1, _hpmf⟩
                    rcases
                        (hIH_e1 hpredlaws hframe'.left.left hwfTm_pure hTmBounded_pure hfp_pure).2
                          μ ρ θ cfg1 (Value.bool b)
                          hθwf hwf_pure hric htagR_pure hmasked_none_pure
                          hmasked_absent_pure hmasked_bounded_pure hbnd_pure hcwr_pure
                          a pm hwfcfg hres hrd ht_e1 hpc
                          hP (hP.closed hroot (SubStep.iteCondPure (f := fuel') hmatch hregime_false))
                      with ⟨θ1, hθext1, _hv1, hric1, hcwr1, _hvalc1, hpres1, _hfresh1, _hrd1, hM1, hF1⟩
                    have hcwr_unmasked :
                        consistentWithRegime predSat ctxᵢ.regime ctxᵢ μ ρ θ :=
                      consistentWithRegimeMasked_unmask
                        (masked := masked) (predSat := predSat)
                        (R := ctxᵢ.regime) (ctx := ctxᵢ)
                        (μ := μ) (ρ := ρ) (θ := θ)
                        hmasked_none hcwr
                    have hb_false : b = false := by
                      exact
                        matchGuard_runtime_branch_alignment
                          predSat tm
                          ctxᵢ μ ρ θ a pm
                          hwfTm hpredlaws hric hcwr_unmasked
                          e1 k deps false b cfg1
                          hmatch hregime_false ht_e1
                    have ht_e3 : terminatesTo e3 cfg1 cf o := by
                      cases hbranch with
                      | inl h =>
                          have : true = false := by rw [← h.1, hb_false]
                          contradiction
                      | inr h => exact h.2
                    have hθ1wf : wfRealizationMap θ1 := hθext1.2 hθwf
                    have hwfcfg1 : wfConfig cfg1 :=
                      (wfConfig_preserved e1 _ cfg1 (Value.bool b) hOp hres.toBelow ht_e1 hwfcfg).1
                    have htc3' : typecheck ctxFalse' e3 fuel' = .ok res3 := by
                      simpa [ctxFalse', ctxFalse, typecheck, Nat.succ_sub_one] using htc3
                    have hwfTm_false : wfTagMeaningCtx tm ctxFalse' := by
                      simpa [ctxFalse', ctxFalse, wfTagMeaningCtx] using hwfTm
                    have hTmBounded_false : TagMeaningBounded tm ctxFalse'.nextTag := by
                      have htc2_tc :
                          typecheck { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩,
                                                nextTag := res1.nextTag',
                                                declaredExternRefs := res1.declared' } e2 fuel' =
                            .ok _res2 := by
                        simpa [typecheck] using _htc2
                      have hle : ctxᵢ.nextTag ≤ _res2.nextTag' :=
                        Nat.le_trans (typecheck_nextTag_mono { ctxᵢ with pureCtx := true } e1 fuel' res1 htc1)
                          (typecheck_nextTag_mono
                            { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩,
                                        nextTag := res1.nextTag',
                                        declaredExternRefs := res1.declared' }
                            e2 fuel' _res2 htc2_tc)
                      simpa [ctxFalse', ctxFalse] using hTmBounded.mono hle
                    have hwf_false : wfTypeContext ctxFalse := by
                      simpa [ctxFalse, wfTypeContext] using hwf
                    have hwf_false' : wfTypeContext ctxFalse' := by
                      have hle : ctxᵢ.nextLoc ≤ _res2.nextLoc' := by
                        have htc2_tc : typecheck { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩,
                                                              nextTag := res1.nextTag',
                                                              declaredExternRefs := res1.declared' } e2 fuel' = .ok _res2 := by
                          simpa [typecheck] using _htc2
                        have := typecheck_nextLoc_mono { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩,
                                                                   nextTag := res1.nextTag',
                                                                   declaredExternRefs := res1.declared' } e2 fuel' _res2 htc2_tc
                        simpa using this
                      simp only [ctxFalse', wfTypeContext]
                      exact ⟨fun l hl => by simp only [ctxFalse] at hl ⊢; exact Nat.lt_of_lt_of_le (hwf_false.1 l hl) hle,
                             varEnvRefLocsBounded_mono hwf_false.2.1 hle,
                             varEnvClosuresCapturedRefLocsBounded_mono hwf_false.2.2 hle⟩
                    have htagR_false : regimeConsistentWithCtxMasked masked ctxFalse := by
                      exact
                        tagEnvConsistentWithRegimeMasked_insert_false
                          masked ctxᵢ.tagEnv ctxᵢ.regime k deps htagR
                    have htagR_false' : regimeConsistentWithCtxMasked masked ctxFalse' := by
                      simpa [ctxFalse', regimeConsistentWithCtxMasked] using htagR_false
                    have hmasked_none_false :
                        ∀ t, masked t → ctxFalse.regime.lookup? t = none := by
                      simpa [ctxFalse] using hmasked_none
                    have hmasked_none_false' :
                        ∀ t, masked t → ctxFalse'.regime.lookup? t = none := by
                      simpa [ctxFalse'] using hmasked_none_false
                    have hmasked_absent_false :
                        MaskedTagsAbsentFromTrueTagEnv masked ctxFalse := by
                      exact
                        MaskedTagsAbsentFromTrueTagEnv_insert_false
                          (masked := masked) (ctx := ctxᵢ) hmasked_absent
                    have hmasked_absent_false' :
                        MaskedTagsAbsentFromTrueTagEnv masked ctxFalse' := by
                      simpa [ctxFalse', MaskedTagsAbsentFromTrueTagEnv] using hmasked_absent_false
                    have hmono_e2 : ctxᵢ.nextTag ≤ _res2.nextTag' :=
                      Nat.le_trans (typecheck_nextTag_mono { ctxᵢ with pureCtx := true } e1 fuel' res1 htc1)
                        (typecheck_normal_nextTag_mono
                          { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩,
                                      nextTag := res1.nextTag',
                                      declaredExternRefs := res1.declared' } e2 fuel' _res2
                          (show typecheck _ e2 _ = _ from _htc2))
                    have hmasked_bounded_false' :
                        ∀ t, masked t → t < ctxFalse'.nextTag := by
                      intro t ht
                      simpa [ctxFalse', ctxFalse] using
                        Nat.lt_of_lt_of_le (hmasked_bounded t ht) hmono_e2
                    have hbnd_false' : TagBoundedCtx ctxFalse' := by
                      obtain ⟨hb_tag, ⟨hb_predV, hb_predM⟩, hb_clos⟩ := hbnd
                      have hk_lt := matchGuard_tag_bounded e1 ctxᵢ.memEnv ctxᵢ.varEnv fuel'
                        k deps ctxᵢ.nextTag hmatch hb_predV hb_predM
                      refine ⟨?_,
                        ⟨predTagsBoundedInVarEnv_mono hb_predV hmono_e2,
                         predTagsBoundedInMemEnv_mono hb_predM hmono_e2⟩,
                        varEnvClosuresCapturedBounded_mono hb_clos hmono_e2⟩
                      exact tagEnvBounded_insert_of_lt ctxᵢ.tagEnv _res2.nextTag' k _
                        (fun j hj => Nat.lt_of_lt_of_le (hb_tag j hj) hmono_e2)
                        (Nat.lt_of_lt_of_le hk_lt hmono_e2)
                    rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
                    have hric1' : runtimeInstantiatesCtx ctxFalse cfg1.memory cfg1.varEnv θ1 := by
                      have hsub : ∀ l, res1.memEnv'.contains l → ctxᵢ.memEnv.contains l := by
                        exact
                          typecheckExpr_pure_mem_subset_of_toPExpr
                            (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
                            hpe1 htc1
                      have hric_true :
                          runtimeInstantiatesCtx
                            { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩ }
                            cfg1.memory cfg1.varEnv θ1 := by
                        exact
                          runtimeInstantiatesCtx_transport_mem_subset_tag_insert_true
                            (ctx := ctxᵢ) (res := res1) (μ := cfg1.memory) (ρ := cfg1.varEnv) (θ := θ1)
                            (k := k) (deps := deps)
                            hsub hric1
                      simpa [ctxFalse, runtimeInstantiatesCtx] using hric_true
                    have hric1'_f : runtimeInstantiatesCtx ctxFalse' cfg1.memory cfg1.varEnv θ1 := by
                      simp only [runtimeInstantiatesCtx, ctxFalse', ctxFalse] at hric1' ⊢; exact hric1'
                    have hcwr1' :
                        consistentWithRegimeMasked masked predSat ctxFalse.regime ctxFalse
                          cfg1.memory cfg1.varEnv θ1 := by
                      have hcwr_true :
                          consistentWithRegimeMasked masked predSat
                            ({ ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩ }).regime
                            ({ ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩ })
                            cfg1.memory cfg1.varEnv θ1 := by
                        refine
                          consistentWithRegimeMasked_transport_ctxAfter_pure_to_ctx_insert_true
                            masked predSat ctxᵢ res1
                            cfg1.memory cfg1.varEnv θ1
                            k deps
                            ?_ ?_ hcwr1
                        · intro k' b' hk
                          exact
                            typecheckExpr_pure_regime_bridge_of_toPExpr
                              (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
                              hpe1 htc1 k' b' hk
                        · intro l qt k' hlookup hguard hRdef
                          exact
                            typecheckExpr_pure_guarded_mem_bridge_of_toPExpr
                              (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
                              hpe1 htc1 l qt k' hlookup hguard hRdef
                      simpa [ctxFalse, consistentWithRegimeMasked] using hcwr_true
                    have hcwr1'_f :
                        consistentWithRegimeMasked masked predSat ctxFalse'.regime ctxFalse'
                          cfg1.memory cfg1.varEnv θ1 := by
                      simp only [consistentWithRegimeMasked, ctxFalse', ctxFalse] at hcwr1' ⊢; exact hcwr1'
                    have hpc_false' : ctxFalse'.pc = true := by
                      simpa [ctxFalse'] using hpc_false
                    have hpredNo : res.qualType.pred = Predicate.noPred := by
                      exact typecheckIf_pred_noPred ctxᵢ e1 e2 e3 (Nat.succ fuel') res htcIf
                    have hle_nl : ctxᵢ.nextLoc ≤ ctxFalse'.nextLoc := by
                      have htc2_tc : typecheck { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩,
                                                            nextTag := res1.nextTag',
                                                            declaredExternRefs := res1.declared' } e2 fuel' = .ok _res2 := by
                        simpa [typecheck] using _htc2
                      exact typecheck_nextLoc_mono { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩,
                                                               nextTag := res1.nextTag',
                                                               declaredExternRefs := res1.declared' } e2 fuel' _res2 htc2_tc
                    have hfp_false : FootprintCtx tm ctxFalse' :=
                      ⟨RecordsCover.matched (b := false) hwfTm hfp.1 hmatch,
                       fun k' d hd l hl => Nat.lt_of_lt_of_le (hfp.2 k' d hd l hl) hle_nl⟩
                    have hIH_e3 := IH' fuel' (by omega) tm masked e3 ctxFalse'
                      (by simpa [ctxFalse', ctxFalse] using hctxTagFalseNext hctxCurrent)
                      hcan3 res3 htc3'
                    -- Thread extern registry.
                    have hreg_cfg1_f : cfg1.registry = registry := by
                      simpa using terminatesTo_preserves_registry ht_e1
                    have hcfg1_eq_f : cfg1 = { memory := cfg1.memory, varEnv := cfg1.varEnv, nextAddr := cfg1.nextAddr, pureMode := cfg1.pureMode, registry := registry } :=
                      config_eq_of_registry cfg1 registry hreg_cfg1_f
                    have hwfcfg1_f : wfConfig { memory := cfg1.memory, varEnv := cfg1.varEnv, nextAddr := cfg1.nextAddr, pureMode := cfg1.pureMode, registry := registry } := by
                      rw [← hcfg1_eq_f]; exact hwfcfg1
                    have ht_e3_f : terminatesTo e3 { memory := cfg1.memory, varEnv := cfg1.varEnv, nextAddr := cfg1.nextAddr, pureMode := cfg1.pureMode, registry := registry } cf o := by
                      rw [← hcfg1_eq_f]; exact ht_e3
                    have hres_cfg1 : RegistryReservedWF registry cfg1.memory cfg1.nextAddr := by
                      apply RegistryReservedWF_mono hres
                      · exact terminatesTo_memory_contains_mono e1
                          { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry }
                          cfg1 (Value.bool b) hOp ht_e1
                      · exact terminatesTo_nextAddr_mono e1
                          { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry }
                          cfg1 (Value.bool b) hOp ht_e1
                    have hrd_false : ReservedDiscipline registry ctxFalse'.declaredExternRefs θ1 := by
                      simp only [ctxFalse']
                      exact ReservedDiscipline.mono_declared
                        (fun id h => typecheck_declared'_mono _ e2 fuel' _res2
                          (by simpa [typecheck] using _htc2) id h)
                        (by simpa [hreg_cfg1_f] using _hrd1)
                    have hroot3f : P ⟨ctxFalse', e3, fuel',
                        { memory := cfg1.memory, varEnv := cfg1.varEnv, nextAddr := cfg1.nextAddr, pureMode := cfg1.pureMode, registry := registry }⟩ := by
                      rw [← hcfg1_eq_f]
                      exact hP.closed hroot (SubStep.iteElseMatched (f := fuel') hmatch hregime_false htc1
                        (by simpa [hb_false] using ht_e1) _htc2)
                    rcases
                        (hIH_e3 hpredlaws hframe'.right hwfTm_false hTmBounded_false hfp_false).2
                          cfg1.memory cfg1.varEnv θ1 cf o
                          hθ1wf hwf_false' hric1'_f htagR_false' hmasked_none_false'
                          hmasked_absent_false' hmasked_bounded_false' hbnd_false' hcwr1'_f
                          cfg1.nextAddr cfg1.pureMode hwfcfg1_f hres_cfg1 hrd_false
                          ht_e3_f hpc_false' hP hroot3f
                      with ⟨θ2, hθext2, hv2, hric2, hcwr2, hvalc2, hpres2, _hfresh2, _hrd2, hM2, hF2⟩
                    have hθext : wfExtendsMap θ θ2 := wfExtendsMap_trans hθext1 hθext2
                    have hctxAfter_memEnv : (ctxAfter ctxᵢ res).memEnv = (ctxAfter ctxFalse' res3).memEnv := by
                      simp [ctxAfter, hmemEnv]
                    have hctxAfter_varEnv : (ctxAfter ctxᵢ res).varEnv = (ctxAfter ctxFalse' res3).varEnv := by
                      simp [ctxAfter, ctxFalse', ctxFalse]
                    have hctxAfter_regime : (ctxAfter ctxᵢ res).regime = (ctxAfter ctxFalse' res3).regime := by
                      simp [ctxAfter, hregime']
                    -- Footprint bookkeeping: compose the condition run and the else-branch run.
                    have hRback : ∀ k' d, tm.lookup k' = some d →
                        (ctxAfter ctxFalse' res3).regime.lookup? k' ≠ none →
                        (ctxAfter ctxPure res1).regime.lookup? k' ≠ none := by
                      intro k' d hd hk'
                      have h := regime_defined_back (regime_monotoneExt ctxFalse' e3 fuel' res3 htc3')
                        hTmBounded_false k' d hd (by simpa [ctxAfter] using hk')
                      cases hl : ctxFalse'.regime.lookup? k' with
                      | none => exact absurd hl h
                      | some b' =>
                          have hb := typecheckExpr_pure_regime_bridge_of_toPExpr
                            (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
                            hpe1 htc1 k' b' (by simpa [ctxFalse', ctxFalse] using hl)
                          simp [ctxAfter, ctxPure, hb]
                    have hM_case : MapKeepsBelow ctxᵢ.nextLoc θ θ2 := hM1.trans hM2 hle_nl
                    have hF_case : KeepsFootprints tm (ctxAfter ctxᵢ res).regime θ μ cf.memory := by
                      rw [hctxAfter_regime]
                      exact KeepsFootprints.trans hF1 hF2 (TagMeaningExtends.refl tm) hθext1.1 hRback
                    have htc3_for_pres :
                        typecheckExpr ctxFalse' e3 fuel' = .ok res3 := by
                      simpa [ctxFalse', ctxFalse] using htc3
                    have hpres_final :
                        PreservesInheritedFinalCleanLocsOneRun ctxᵢ res μ cf.memory θ θ2 := by
                      refine ⟨?_⟩
                      intro l qt_in qt_out hlookup_in hlookup_out hclean_out
                      rcases
                          typecheckExpr_clean_lookup_origin_of_pc_true
                            ctxFalse' e3 fuel' res3 htc3_for_pres hwf_false' hbnd_false' hpc_false'
                            l qt_out (by simpa [hmemEnv] using hlookup_out)
                            (by simpa [ctxFalse', ctxFalse] using memEnv_contains_of_lookup_some ctxᵢ.memEnv l qt_in hlookup_in)
                            (by simpa [hregime'] using hclean_out)
                        with ⟨qt_mid, hlookup_mid_false, hclean_mid_false⟩
                      have hlookup_mid_res1 : res1.memEnv'.lookup l = some qt_mid := by
                        exact
                          typecheckExpr_pure_mem_lookup_bridge_of_toPExpr
                            (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
                            hpe1 htc1 l qt_mid (by simpa [ctxFalse] using hlookup_mid_false)
                      have hclean_mid_res1 : qtypCleanUnder res1.regime' qt_mid := by
                        exact
                          qtypCleanUnder_transport_pure_regime_of_toPExpr
                            ctxᵢ e1 pe1 fuel' res1 hpe1 htc1 qt_mid
                            (by simpa [ctxFalse] using hclean_mid_false)
                      have hpres_mid :
                          PreservesInheritedCleanLocOneRun μ cfg1.memory θ θ1 l :=
                        PreservesInheritedFinalCleanLocsOneRun.apply
                          (ctx := ctxPure) (res := res1)
                          (μ_in := μ) (μ_out := cfg1.memory) (θ_in := θ) (θ_out := θ1)
                          hpres1
                          (by simpa [ctxPure] using hlookup_in)
                          hlookup_mid_res1
                          hclean_mid_res1
                      have hpres_last :
                          PreservesInheritedCleanLocOneRun cfg1.memory cf.memory θ1 θ2 l :=
                        PreservesInheritedFinalCleanLocsOneRun.apply
                          (ctx := ctxFalse') (res := res3)
                          (μ_in := cfg1.memory) (μ_out := cf.memory) (θ_in := θ1) (θ_out := θ2)
                          hpres2
                          hlookup_mid_false
                          (by simpa [hmemEnv] using hlookup_out)
                          (by simpa [hregime'] using hclean_out)
                      exact PreservesInheritedCleanLocOneRun.trans hpres_mid hpres_last
                    have hfresh_final : FreshCleanLocsUnrealizedOneRun ctxᵢ res θ2 := by
                      intro l qt hnotIn hlookup hclean
                      exact _hfresh2 l qt (by simpa [ctxFalse', ctxFalse] using hnotIn)
                        (by simpa [hmemEnv] using hlookup) (by simpa [hregime'] using hclean)
                    refine ⟨θ2, hθext, ?_, ?_, ?_, ?_, hpres_final, hfresh_final, ?_, hM_case, hF_case⟩
                    · simpa [hetyp] using hv2
                    · simp only [runtimeInstantiatesCtx, hctxAfter_memEnv, hctxAfter_varEnv]
                      exact hric2
                    · simp only [consistentWithRegimeMasked, hctxAfter_regime, hctxAfter_memEnv,
                        hctxAfter_varEnv]
                      exact hcwr2
                    · refine valueConsistentWithRegimeMasked.noTag ?_ ?_
                      · simp [qtypGuardTag, hpredNo]
                      ·
                        have hcap2 :
                            closureCapturedVarsRegimeMasked masked predSat
                              (ctxAfter ctxFalse' res3).regime
                              res3.qualType cf.memory θ2 o :=
                          valueConsistentWithRegimeMasked_closureCapturedVarsRegime hvalc2
                        have hcap2' :
                            closureCapturedVarsRegimeMasked masked predSat
                              (ctxAfter ctxᵢ res).regime
                              res3.qualType cf.memory θ2 o := by
                          rwa [hctxAfter_regime]
                        exact
                          closureCapturedVarsRegimeMasked_transport_etyp
                            (qt := res3.qualType) (qt' := res.qualType)
                            hetyp.symm hcap2'
                    · -- ReservedDiscipline: result set is exactly the executed arm's
                      rw [hdecl']
                      exact _hrd2
                  · obtain ⟨hstdCase, res1, htc1, hbool, res2, htc2, res3, htc3,
                      hmemEnv, htagEnv, hnextLoc, hnextTag, hregime', hdecl', hpoison, hetyp, hpred⟩ := hstd
                    have hlogArm := typecheckIf_tagLog_std htcIf hstdCase htc1 htc2 htc3
                    intro hpredlaws hframe hwfTm hTmBounded hfp
                    have hframe' := hframe.of_log_eq hlogArm
                    refine ⟨?_, ?_⟩
                    · exact
                        StepFRSingleRunTagMeaningPost.of_typecheck_preserves
                          predSat tm ctxᵢ (Expr.ite e1 e2 e3)
                          (Nat.succ (Nat.succ fuel')) res
                          hwfTm hTmBounded hframe htc
                    intro μ ρ θ cf o hθwf hwf hric htagR hmasked_none hmasked_absent hmasked_bounded hbnd hcwr a pm hwfcfg hres hrd ht hpc P hP hroot
                    have hstdArm : StdArm ctxᵢ e1 fuel' := by simpa [StdArm] using hstdCase.symm
                    let ctx' : TypeContext := ctxAfter ctxᵢ res1
                    let pc' := joinPoison ctxᵢ.pc res1.qualType.poison
                    let ctx'' : TypeContext := { ctx' with pc := pc' }
                    let ctxForE3 : TypeContext := { ctx'' with nextLoc := res2.nextLoc', nextTag := res2.nextTag',
                                                               declaredExternRefs := res2.declared' }
                    have htc1' : typecheck ctxᵢ e1 fuel' = .ok res1 := by
                      simpa [typecheck, Nat.succ_sub_one] using htc1
                    have hIH_e1 := IH' fuel' (by omega) tm masked e1 ctxᵢ
                      hctxCurrent hcan1 res1 htc1'
                    have hctxStdThen : CtxReach ctx'' := by
                      simpa [ctx'', ctx', pc'] using
                        hctxAfterPc (ctx := ctxᵢ) (res := res1) (pc := pc') hctxCurrent
                    have hctxStdElse : CtxReach ctxForE3 := by
                      simpa [ctxForE3] using
                        hctxNext (ctx := ctx'') (nextLoc := res2.nextLoc')
                          (nextTag := res2.nextTag') hctxStdThen
                    have hIH_e1_inst := hIH_e1 hpredlaws hframe'.left.left hwfTm hTmBounded hfp
                    rcases hIH_e1_inst.1 with ⟨tm1, hcanon1, hpredlaws1, _hresTm1, hwfTm1, hwithin1⟩
                    have hstruct_rt := terminatesTo_ite_inv' e1 e2 e3
                      { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm,
                        registry := registry } cf o ht
                    rcases hstruct_rt with ⟨cfg1, b, ht_e1, hbranch, _hpm1, _hpmf⟩
                    rcases
                        hIH_e1_inst.2 μ ρ θ cfg1 (Value.bool b)
                          hθwf hwf hric htagR hmasked_none hmasked_absent hmasked_bounded hbnd hcwr
                          a pm hwfcfg hres hrd ht_e1 hpc
                          hP (hP.closed hroot (SubStep.iteCondStd (f := fuel') hstdArm))
                      with ⟨θ1, hθext1, hv1, hric1, hcwr1, hvalc1, hpres1, _hfresh1, _hrd1, hM1, hF1⟩
                    have hθ1wf : wfRealizationMap θ1 := hθext1.2 hθwf
                    have hwfcfg1 : wfConfig cfg1 :=
                      (wfConfig_preserved e1 _ cfg1 (Value.bool b) hOp hres.toBelow ht_e1 hwfcfg).1
                    have hres_cfg1 : RegistryReservedWF registry cfg1.memory cfg1.nextAddr := by
                      apply RegistryReservedWF_mono hres
                      · exact terminatesTo_memory_contains_mono e1
                          { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry }
                          cfg1 (Value.bool b) hOp ht_e1
                      · exact terminatesTo_nextAddr_mono e1
                          { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry }
                          cfg1 (Value.bool b) hOp ht_e1
                    have hmono1 :
                        Regime.monotoneStepExt ctxᵢ.regime (ctxAfter ctxᵢ res1).regime
                          (fun k => ctxᵢ.nextTag ≤ k) :=
                      regime_monotoneExt ctxᵢ e1 fuel' res1 htc1'
                    have htagR1 :
                        regimeConsistentWithCtxMasked masked (ctxAfter ctxᵢ res1) :=
                      typecheckExpr_preserves_regimeConsistentWithCtxMasked
                        masked ctxᵢ e1 fuel' res1 htagR htc1'
                    have hmasked_none1 :
                        ∀ t, masked t → (ctxAfter ctxᵢ res1).regime.lookup? t = none :=
                      masked_lookup_none_of_monotoneStepExt hmasked_none
                        (fun t ht => Nat.not_le.2 (hmasked_bounded t ht)) hmono1
                    have hmasked_absent1 :
                        MaskedTagsAbsentFromTrueTagEnv masked (ctxAfter ctxᵢ res1) :=
                      typecheckExpr_preserves_MaskedTagsAbsentFromTrueTagEnv
                        masked ctxᵢ e1 fuel' res1 hmasked_absent hmasked_none hmasked_bounded htc1'
                    have hTmBounded1 : TagMeaningBounded tm1 (ctxAfter ctxᵢ res1).nextTag := by
                      simpa [ctxAfter] using IsCanonicalExtension.bounded hcanon1
                    have hwf1 : wfTypeResult res1 :=
                      typecheckExpr_preserves_wfTypeResult ctxᵢ e1 fuel' res1 hwf htc1'
                    have hwf_ctx' : wfTypeContext ctx' := by
                      simpa [ctx'] using wfTypeContext_of_wfTypeResult ctxᵢ res1 hwf1 hwf
                        (typecheck_nextLoc_mono ctxᵢ e1 fuel' res1 htc1')
                    have hwfTm_ctx'' : wfTagMeaningCtx tm1 ctx'' := by
                      simpa [ctx'', ctx', pc'] using! hwfTm1
                    have hTmBounded_ctx'' : TagMeaningBounded tm1 ctx''.nextTag := by
                      simpa [ctx'', ctx', pc'] using hTmBounded1
                    have hwf_ctx'' : wfTypeContext ctx'' := by
                      simpa [ctx'', ctx', pc', wfTypeContext] using hwf_ctx'
                    have hric1_ctx'' :
                        runtimeInstantiatesCtx ctx'' cfg1.memory cfg1.varEnv θ1 := by
                      simpa [ctx'', ctx', pc', ctxAfter, runtimeInstantiatesCtx] using hric1
                    have hcwr1_ctx'' :
                        consistentWithRegimeMasked masked predSat ctx''.regime ctx''
                          cfg1.memory cfg1.varEnv θ1 := by
                      simpa [ctx'', ctx', pc', ctxAfter, consistentWithRegimeMasked] using hcwr1
                    have htagR_ctx'' : regimeConsistentWithCtxMasked masked ctx'' := by
                      simpa [ctx'', ctx', pc', regimeConsistentWithCtxMasked] using htagR1
                    have hmasked_none_ctx'' :
                        ∀ t, masked t → ctx''.regime.lookup? t = none := by
                      simpa [ctx'', ctx', pc', ctxAfter] using hmasked_none1
                    have hmasked_absent_ctx'' :
                        MaskedTagsAbsentFromTrueTagEnv masked ctx'' := by
                      simpa [ctx'', ctx', pc', ctxAfter, MaskedTagsAbsentFromTrueTagEnv] using
                        hmasked_absent1
                    have hmono_e1_tag : ctxᵢ.nextTag ≤ res1.nextTag' :=
                      typecheck_nextTag_mono ctxᵢ e1 fuel' res1 (by simpa [typecheck] using htc1')
                    have hbnd_ctx'' : TagBoundedCtx ctx'' := by
                      simpa [ctx'', ctx', pc', ctxAfter] using!
                        typecheckExpr_preserves_TagBoundedCtx ctxᵢ e1 fuel' res1
                          (by simpa [typecheck] using htc1') hbnd
                    have hmasked_bounded_ctx'' :
                        ∀ t, masked t → t < ctx''.nextTag := by
                      intro t ht
                      simpa [ctx'', ctx', pc', ctxAfter] using
                        Nat.lt_of_lt_of_le (hmasked_bounded t ht) hmono_e1_tag
                    have hpc'' : ctx''.pc = true := by
                      simp [ctx'', pc', hpc, joinPoison]
                    have hnextLoc_mono :
                        res1.nextLoc' ≤ res2.nextLoc' := by
                      have : ctx''.nextLoc ≤ res2.nextLoc' :=
                        typecheck_nextLoc_mono ctx'' e2 fuel' res2
                          (by simpa [ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using! htc2)
                      simpa [ctx'', ctx'] using! this
                    have hnextTag_mono :
                        res1.nextTag' ≤ res2.nextTag' := by
                      have : ctx''.nextTag ≤ res2.nextTag' :=
                        typecheck_nextTag_mono ctx'' e2 fuel' res2
                          (by simpa [ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using! htc2)
                      simpa [ctx'', ctx'] using! this
                    have hfp1 : FootprintCtx tm1 (ctxAfter ctxᵢ res1) :=
                      hkeepFP.apply htc1 hwfTm hTmBounded hbnd hwf
                        (IsCanonicalExtension.extends_tm hcanon1) hwithin1 hfp
                    have hfp_ctx'' : FootprintCtx tm1 ctx'' := hfp1
                    have hfp_ctxForE3 : FootprintCtx tm1 ctxForE3 :=
                      ⟨hfp1.1, fun k d hd l hl => Nat.lt_of_lt_of_le (hfp1.2 k d hd l hl) hnextLoc_mono⟩
                    have hTmBounded_ctxForE3 : TagMeaningBounded tm1 ctxForE3.nextTag := by
                      simpa [ctxForE3, ctx'', ctx', pc'] using hTmBounded1.mono hnextTag_mono
                    have hwfTm_ctxForE3 : wfTagMeaningCtx tm1 ctxForE3 := by
                      simpa [ctxForE3, ctx'', ctx', pc'] using! hwfTm1
                    have hwf_ctxForE3 : wfTypeContext ctxForE3 := by
                      simp only [ctxForE3, wfTypeContext]
                      exact ⟨fun l hl => by simp only [ctx'', ctx', ctxAfter] at hl ⊢; exact Nat.lt_of_lt_of_le (hwf_ctx'.1 l hl) hnextLoc_mono,
                             varEnvRefLocsBounded_mono hwf_ctx'.2.1 hnextLoc_mono,
                             varEnvClosuresCapturedRefLocsBounded_mono hwf_ctx'.2.2 hnextLoc_mono⟩
                    have hric1_ctxForE3 :
                        runtimeInstantiatesCtx ctxForE3 cfg1.memory cfg1.varEnv θ1 := by
                      simpa [ctxForE3, ctx'', ctx', pc', ctxAfter, runtimeInstantiatesCtx] using hric1
                    have hcwr1_ctxForE3 :
                        consistentWithRegimeMasked masked predSat ctxForE3.regime ctxForE3
                          cfg1.memory cfg1.varEnv θ1 := by
                      simpa [ctxForE3, ctx'', ctx', pc', ctxAfter, consistentWithRegimeMasked] using hcwr1
                    have htagR_ctxForE3 : regimeConsistentWithCtxMasked masked ctxForE3 := by
                      show tagEnvConsistentWithRegimeMasked masked ctxForE3.tagEnv ctxForE3.regime
                      simpa [ctxForE3, ctx'', ctx', pc', regimeConsistentWithCtxMasked] using htagR1
                    have hmasked_none_ctxForE3 :
                        ∀ t, masked t → ctxForE3.regime.lookup? t = none := by
                      simpa [ctxForE3, ctx'', ctx', pc', ctxAfter] using hmasked_none1
                    have hmasked_absent_ctxForE3 :
                        MaskedTagsAbsentFromTrueTagEnv masked ctxForE3 := by
                      simpa [ctxForE3, ctx'', ctx', pc', ctxAfter, MaskedTagsAbsentFromTrueTagEnv] using
                        hmasked_absent1
                    have hbnd_ctxForE3 : TagBoundedCtx ctxForE3 := by
                      obtain ⟨hb_tag, ⟨hb_predV, hb_predM⟩, hb_clos⟩ := hbnd_ctx''
                      exact ⟨tagEnvBounded_mono _ _ _ hb_tag hnextTag_mono,
                        ⟨predTagsBoundedInVarEnv_mono hb_predV hnextTag_mono,
                         predTagsBoundedInMemEnv_mono hb_predM hnextTag_mono⟩,
                        varEnvClosuresCapturedBounded_mono hb_clos hnextTag_mono⟩
                    have hmasked_bounded_ctxForE3 :
                        ∀ t, masked t → t < ctxForE3.nextTag := by
                      intro t ht
                      simpa [ctxForE3, ctx'', ctx', pc', ctxAfter] using
                        Nat.lt_of_lt_of_le (hmasked_bounded_ctx'' t ht) hnextTag_mono
                    have hpcForE3 : ctxForE3.pc = true := by
                      simp [ctxForE3, ctx'', pc', hpc, joinPoison]
                    have htc2' : typecheck ctx'' e2 fuel' = .ok res2 := by
                      simpa [ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using! htc2
                    have htc3' : typecheck ctxForE3 e3 fuel' = .ok res3 := by
                      simpa [ctxForE3, ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using! htc3
                    have hpredNo : res.qualType.pred = Predicate.noPred := by
                      exact typecheckIf_pred_noPred ctxᵢ e1 e2 e3 (Nat.succ fuel') res htcIf
                    have hcompat23 : beqETypSignature res2.qualType.etyp res3.qualType.etyp = true :=
                      typecheckIf_standard_compat_from_existing_hyps
                        ctxᵢ e1 e2 e3 fuel' res res1 res2 res3
                        hstdCase htc1 hbool htc2 htc3 htcIf
                    match (show True from trivial) with
                    | _ =>
                        have hclean_back_mid :
                            ∀ l qt_in qt_out,
                              ctxᵢ.memEnv.lookup l = some qt_in →
                              res.memEnv'.lookup l = some qt_out →
                              qtypCleanUnder res.regime' qt_out →
                              ∃ qt_mid,
                                res1.memEnv'.lookup l = some qt_mid ∧
                                qtypCleanUnder res1.regime' qt_mid := by
                          intro l _qt_in qt_out _hlookup_in hlookup_out hclean_out
                          have hlookup_join :
                              (joinMemEnvsStrong res2.memEnv' res3.memEnv').lookup l = some qt_out := by
                            simpa [hmemEnv] using hlookup_out
                          cases hclean_out with
                          | clean hpoison_out =>
                              have hcontains_join :
                                  (joinMemEnvsStrong res2.memEnv' res3.memEnv').contains l :=
                                memEnv_contains_of_lookup_some
                                  (joinMemEnvsStrong res2.memEnv' res3.memEnv') l qt_out hlookup_join
                              rcases
                                  joinMemEnvsStrong_contains_implies_or
                                    res2.memEnv' res3.memEnv' l hcontains_join
                                with hcontains2 | hcontains3
                              · rcases memEnv_lookup_some_of_contains res2.memEnv' l hcontains2 with
                                  ⟨qt2, hlookup2⟩
                                have henv2 : res2.memEnv'.lookup l ≠ none := by
                                  intro hnone
                                  rw [hlookup2] at hnone
                                  contradiction
                                rcases
                                    joinMemEnvsStrong_lookup_clean_left
                                      res2.memEnv' res3.memEnv' l qt_out
                                      hlookup_join hpoison_out henv2
                                  with ⟨qt2', hlookup2', _hetyp2, hpoison2⟩
                                exact
                                  typecheckExpr_clean_lookup_origin_of_pc_true
                                    ctx'' e2 fuel' res2 htc2' hwf_ctx'' hbnd_ctx'' hpc''
                                    l qt2' hlookup2'
                                    (by simpa [ctx'', ctx', ctxAfter] using typecheckExpr_mem_contains_preserved ctxᵢ e1 fuel' res1 htc1' l (memEnv_contains_of_lookup_some ctxᵢ.memEnv l _qt_in _hlookup_in))
                                    (qtypCleanUnder.clean hpoison2)
                              · rcases memEnv_lookup_some_of_contains res3.memEnv' l hcontains3 with
                                  ⟨qt3, hlookup3⟩
                                have henv3 : res3.memEnv'.lookup l ≠ none := by
                                  intro hnone
                                  rw [hlookup3] at hnone
                                  contradiction
                                rcases
                                    joinMemEnvsStrong_lookup_clean_right
                                      res2.memEnv' res3.memEnv' l qt_out
                                      hlookup_join hpoison_out henv3
                                  with ⟨qt3', hlookup3', _hetyp3, hpoison3⟩
                                exact
                                  typecheckExpr_clean_lookup_origin_of_pc_true
                                    ctxForE3 e3 fuel' res3 htc3' hwf_ctxForE3 hbnd_ctxForE3 hpcForE3
                                    l qt3' hlookup3'
                                    (by simpa [ctxForE3, ctx'', ctx', ctxAfter] using typecheckExpr_mem_contains_preserved ctxᵢ e1 fuel' res1 htc1' l (memEnv_contains_of_lookup_some ctxᵢ.memEnv l _qt_in _hlookup_in))
                                    (qtypCleanUnder.clean hpoison3)
                          | guard k htag hk hnotfun =>
                              have hk_join :
                                  (joinRegimes res2.regime' res3.regime').lookup? k = some true := by
                                simpa [hregime'] using hk
                              have hcontains_join :
                                  (joinMemEnvsStrong res2.memEnv' res3.memEnv').contains l :=
                                memEnv_contains_of_lookup_some
                                  (joinMemEnvsStrong res2.memEnv' res3.memEnv') l qt_out hlookup_join
                              rcases
                                  joinMemEnvsStrong_contains_implies_or
                                    res2.memEnv' res3.memEnv' l hcontains_join
                                with hcontains2 | hcontains3
                              · rcases memEnv_lookup_some_of_contains res2.memEnv' l hcontains2 with
                                  ⟨qt2, hlookup2⟩
                                have htag2 : qtypGuardTag qt2 = some k :=
                                  joinMemEnvsStrong_lookup_guardTag_left
                                    res2.memEnv' res3.memEnv' l qt_out qt2 k
                                    hlookup_join hlookup2 htag
                                have hk2 : res2.regime'.lookup? k = some true :=
                                  joinRegimes_lookup_some_left
                                    res2.regime' res3.regime' k true hk_join
                                have hnotfun2 : qt2.etyp.isFunctionType = false := by
                                  rw [memEnv_lookup_etyp_int res2.memEnv' l qt2 hlookup2]
                                  decide
                                exact
                                  typecheckExpr_clean_lookup_origin_of_pc_true
                                    ctx'' e2 fuel' res2 htc2' hwf_ctx'' hbnd_ctx'' hpc''
                                    l qt2 hlookup2
                                    (by simpa [ctx'', ctx', ctxAfter] using typecheckExpr_mem_contains_preserved ctxᵢ e1 fuel' res1 htc1' l (memEnv_contains_of_lookup_some ctxᵢ.memEnv l _qt_in _hlookup_in))
                                    (qtypCleanUnder.guard k htag2 hk2 hnotfun2)
                              · rcases memEnv_lookup_some_of_contains res3.memEnv' l hcontains3 with
                                  ⟨qt3, hlookup3⟩
                                have htag3 : qtypGuardTag qt3 = some k :=
                                  joinMemEnvsStrong_lookup_guardTag_right
                                    res2.memEnv' res3.memEnv' l qt_out qt3 k
                                    hlookup_join hlookup3 htag
                                have hk3 : res3.regime'.lookup? k = some true :=
                                  joinRegimes_lookup_some_right
                                    res2.regime' res3.regime' k true hk_join
                                have hnotfun3 : qt3.etyp.isFunctionType = false := by
                                  rw [memEnv_lookup_etyp_int res3.memEnv' l qt3 hlookup3]
                                  decide
                                exact
                                  typecheckExpr_clean_lookup_origin_of_pc_true
                                    ctxForE3 e3 fuel' res3 htc3' hwf_ctxForE3 hbnd_ctxForE3 hpcForE3
                                    l qt3 hlookup3
                                    (by simpa [ctxForE3, ctx'', ctx', ctxAfter] using typecheckExpr_mem_contains_preserved ctxᵢ e1 fuel' res1 htc1' l (memEnv_contains_of_lookup_some ctxᵢ.memEnv l _qt_in _hlookup_in))
                                    (qtypCleanUnder.guard k htag3 hk3 hnotfun3)
                        -- Footprint bookkeeping shared by the two branches.
                        have hnl_e1 : ctxᵢ.nextLoc ≤ res1.nextLoc' :=
                          typecheck_nextLoc_mono ctxᵢ e1 fuel' res1 htc1'
                        have hnl_then : ctxᵢ.nextLoc ≤ ctx''.nextLoc := hnl_e1
                        have hnl_else : ctxᵢ.nextLoc ≤ ctxForE3.nextLoc :=
                          Nat.le_trans hnl_e1 hnextLoc_mono
                        have hRleft : ∀ k d, tm1.lookup k = some d →
                            (ctxAfter ctxᵢ res).regime.lookup? k ≠ none →
                            (ctxAfter ctx'' res2).regime.lookup? k ≠ none := by
                          intro k d _ hk h2
                          change res.regime'.lookup? k ≠ none at hk
                          change res2.regime'.lookup? k = none at h2
                          rw [hregime'] at hk
                          cases hj : (joinRegimes res2.regime' res3.regime').lookup? k with
                          | none => exact hk hj
                          | some b' =>
                              have h := joinRegimes_lookup_some_left res2.regime' res3.regime' k b' hj
                              rw [h2] at h
                              cases h
                        have hRright : ∀ k d, tm1.lookup k = some d →
                            (ctxAfter ctxᵢ res).regime.lookup? k ≠ none →
                            (ctxAfter ctxForE3 res3).regime.lookup? k ≠ none := by
                          intro k d _ hk h3
                          change res.regime'.lookup? k ≠ none at hk
                          change res3.regime'.lookup? k = none at h3
                          rw [hregime'] at hk
                          cases hj : (joinRegimes res2.regime' res3.regime').lookup? k with
                          | none => exact hk hj
                          | some b' =>
                              have h := joinRegimes_lookup_some_right res2.regime' res3.regime' k b' hj
                              rw [h3] at h
                              cases h
                        have hRback : ∀ k d, tm.lookup k = some d →
                            (ctxAfter ctxᵢ res).regime.lookup? k ≠ none →
                            (ctxAfter ctxᵢ res1).regime.lookup? k ≠ none := by
                          intro k d hd hk
                          exact regime_defined_back (regime_monotoneExt ctx'' e2 fuel' res2 htc2')
                            (TagMeaningBounded.mono hTmBounded hmono_e1_tag) k d hd (hRleft k d
                              (TagMeaningExtends.lookup (IsCanonicalExtension.extends_tm hcanon1) hd) hk)
                        cases hbranch with
                          | inl hbranch_true =>
                              have ht_e2 : terminatesTo e2 cfg1 cf o := hbranch_true.2
                              have hIH_e2 := IH' fuel' (by omega) tm1 masked e2 ctx''
                                hctxStdThen hcan2 res2 htc2'
                              -- Thread extern registry.
                              have hreg_cfg1_std2 : cfg1.registry = registry := by
                                simpa using terminatesTo_preserves_registry ht_e1
                              have hcfg1_eq_std2 : cfg1 = { memory := cfg1.memory, varEnv := cfg1.varEnv, nextAddr := cfg1.nextAddr, pureMode := cfg1.pureMode, registry := registry } :=
                                config_eq_of_registry cfg1 registry hreg_cfg1_std2
                              have hwfcfg1_std2 : wfConfig { memory := cfg1.memory, varEnv := cfg1.varEnv, nextAddr := cfg1.nextAddr, pureMode := cfg1.pureMode, registry := registry } := by
                                rw [← hcfg1_eq_std2]; exact hwfcfg1
                              have ht_e2_std2 : terminatesTo e2 { memory := cfg1.memory, varEnv := cfg1.varEnv, nextAddr := cfg1.nextAddr, pureMode := cfg1.pureMode, registry := registry } cf o := by
                                rw [← hcfg1_eq_std2]; exact ht_e2
                              have hrd_ctx'' : ReservedDiscipline registry ctx''.declaredExternRefs θ1 := by
                                simp only [ctx'', ctx', ctxAfter]
                                simpa [hreg_cfg1_std2] using _hrd1
                              have hroot2std : P ⟨ctx'', e2, fuel',
                                  { memory := cfg1.memory, varEnv := cfg1.varEnv, nextAddr := cfg1.nextAddr, pureMode := cfg1.pureMode, registry := registry }⟩ := by
                                rw [← hcfg1_eq_std2]
                                exact hP.closed hroot (SubStep.iteThenStd (f := fuel') hstdArm htc1
                                  (by simpa [hbranch_true.1] using ht_e1))
                              rcases
                                  (hIH_e2 hpredlaws1 (hframe'.left.next hwithin1) hwfTm_ctx''
                                    hTmBounded_ctx'' hfp_ctx'').2
                                    cfg1.memory cfg1.varEnv θ1 cf o
                                    hθ1wf hwf_ctx'' hric1_ctx'' htagR_ctx'' hmasked_none_ctx''
                                    hmasked_absent_ctx'' hmasked_bounded_ctx'' hbnd_ctx'' hcwr1_ctx''
                                    cfg1.nextAddr cfg1.pureMode hwfcfg1_std2 hres_cfg1 hrd_ctx'' ht_e2_std2 hpc''
                                    hP hroot2std
                                with ⟨θ2, hθext2, hv2, hric2, hcwr2, hvalc2, hpres2, _hfresh2, _hrd2, hM2, hF2⟩
                              have hθext : wfExtendsMap θ θ2 := wfExtendsMap_trans hθext1 hθext2
                              have hM_case : MapKeepsBelow ctxᵢ.nextLoc θ θ2 := hM1.trans hM2 hnl_then
                              have hF_case : KeepsFootprints tm (ctxAfter ctxᵢ res).regime θ μ cf.memory :=
                                KeepsFootprints.trans hF1 (KeepsFootprints.mono_regime hF2 hRleft)
                                  (IsCanonicalExtension.extends_tm hcanon1) hθext1.1 hRback
                              have hcwr2_left :
                                  consistentWithRegimeMasked masked predSat
                                    (ctxAfter ctxᵢ res2).regime
                                    (ctxAfter ctxᵢ res2)
                                    cf.memory cf.varEnv θ2 := by
                                simpa [ctx'', ctx', pc', ctxAfter, consistentWithRegimeMasked] using hcwr2
                              have hcwr_final :
                                  consistentWithRegimeMasked masked predSat
                                    (ctxAfter ctxᵢ res).regime
                                    (ctxAfter ctxᵢ res)
                                    cf.memory cf.varEnv θ2 := by
                                exact
                                  consistentWithRegimeMasked_join_from_left
                                    masked predSat ctxᵢ
                                    res2 res3 res
                                    cf.memory cf.varEnv θ2
                                    hmemEnv hregime' hcwr2_left
                              have hric_final :
                                  runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf.memory cf.varEnv θ2 := by
                                unfold runtimeInstantiatesCtx at hric2 ⊢
                                constructor
                                · intro l a hθlookup
                                  rcases hric2.1 l a hθlookup with ⟨hcontains2, hmem⟩
                                  rcases
                                      memEnv_lookup_some_of_contains
                                        (ctxAfter ctx'' res2).memEnv l hcontains2
                                    with ⟨qt2, hlookup2ctx⟩
                                  have hlookup2 : res2.memEnv'.lookup l = some qt2 := by
                                    simpa [ctxAfter] using hlookup2ctx
                                  rcases
                                      joinMemEnvsStrong_lookup_some_of_left_lookup
                                        res2.memEnv' res3.memEnv' l qt2 hlookup2
                                    with ⟨qt, hlookup_join⟩
                                  have hcontains_join :
                                      (joinMemEnvsStrong res2.memEnv' res3.memEnv').contains l := by
                                    exact
                                      memEnv_contains_of_lookup_some
                                        (joinMemEnvsStrong res2.memEnv' res3.memEnv') l qt hlookup_join
                                  exact ⟨by simpa [ctxAfter, hmemEnv] using hcontains_join, hmem⟩
                                · intro x qt hlookup
                                  have hlookup' :
                                      (ctxAfter ctx'' res2).varEnv.lookup x = some qt := by
                                    simpa [ctxAfter, ctx'', ctx', pc'] using hlookup
                                  exact hric2.2 hlookup'
                              have hpres_branch_final :
                                  PreservesInheritedFinalCleanLocsOneRun
                                    (ctxAfter ctxᵢ res1) res
                                    cfg1.memory cf.memory θ1 θ2 := by
                                refine ⟨?_⟩
                                intro l qt_in qt_out hlookup_in hlookup_out hclean_out
                                have hlookup_join :
                                    (joinMemEnvsStrong res2.memEnv' res3.memEnv').lookup l = some qt_out := by
                                  simpa [hmemEnv] using hlookup_out
                                have hcontains_in :
                                    (ctxAfter ctxᵢ res1).memEnv.contains l := by
                                  exact
                                    memEnv_contains_of_lookup_some
                                      (ctxAfter ctxᵢ res1).memEnv l qt_in
                                      (by simpa [ctxAfter] using hlookup_in)
                                have hcontains2 : res2.memEnv'.contains l :=
                                  typecheckExpr_mem_contains_preserved
                                    ctx'' e2 fuel' res2
                                    (by simpa [ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using! htc2)
                                    l
                                    (by simpa [ctx'', ctx', pc', ctxAfter] using hcontains_in)
                                rcases memEnv_lookup_some_of_contains res2.memEnv' l hcontains2 with
                                  ⟨qt2, hlookup2⟩
                                have hclean2 : qtypCleanUnder res2.regime' qt2 := by
                                  cases hclean_out with
                                  | clean hpoison_out =>
                                      have henv2 : res2.memEnv'.lookup l ≠ none := by
                                        intro hnone
                                        rw [hlookup2] at hnone
                                        contradiction
                                      rcases
                                          joinMemEnvsStrong_lookup_clean_left
                                            res2.memEnv' res3.memEnv' l qt_out
                                            hlookup_join hpoison_out henv2
                                        with ⟨qt2', hlookup2', _hetyp2, hpoison2⟩
                                      have hqt2 : qt2 = qt2' := by
                                        rw [hlookup2] at hlookup2'
                                        injection hlookup2'
                                      cases hqt2
                                      exact qtypCleanUnder.clean hpoison2
                                  | guard k htag hk hnotfun =>
                                      have hk_join :
                                          (joinRegimes res2.regime' res3.regime').lookup? k = some true := by
                                        simpa [hregime'] using hk
                                      have htag2 : qtypGuardTag qt2 = some k :=
                                        joinMemEnvsStrong_lookup_guardTag_left
                                          res2.memEnv' res3.memEnv' l qt_out qt2 k
                                          hlookup_join hlookup2 htag
                                      have hk2 : res2.regime'.lookup? k = some true :=
                                        joinRegimes_lookup_some_left
                                          res2.regime' res3.regime' k true hk_join
                                      have hnotfun2 : qt2.etyp.isFunctionType = false := by
                                        rw [memEnv_lookup_etyp_int res2.memEnv' l qt2 hlookup2]
                                        decide
                                      exact qtypCleanUnder.guard k htag2 hk2 hnotfun2
                                exact
                                  PreservesInheritedFinalCleanLocsOneRun.apply
                                    (ctx := ctx'') (res := res2)
                                    (μ_in := cfg1.memory) (μ_out := cf.memory)
                                    (θ_in := θ1) (θ_out := θ2)
                                    hpres2
                                    (by simpa [ctx'', ctx', pc', ctxAfter] using hlookup_in)
                                    hlookup2
                                    hclean2
                              have hpres_final :
                                  PreservesInheritedFinalCleanLocsOneRun
                                    ctxᵢ res μ cf.memory θ θ2 := by
                                exact
                                  PreservesInheritedFinalCleanLocsOneRun.compose
                                    (ctx := ctxᵢ) (res1 := res1) (res2 := res)
                                    hclean_back_mid hpres1
                                    (by simpa [ctx'] using hpres_branch_final)
                              have hfresh_final :
                                  FreshCleanLocsUnrealizedOneRun ctxᵢ res θ2 := by
                                intro l qt hnotIn hlookup hclean
                                have hlookup_join :
                                    (joinMemEnvsStrong res2.memEnv' res3.memEnv').lookup l = some qt := by
                                  simpa [hmemEnv] using hlookup
                                by_cases hcontains2 : res2.memEnv'.contains l
                                · rcases memEnv_lookup_some_of_contains res2.memEnv' l hcontains2 with
                                    ⟨qt2, hlookup2⟩
                                  have hclean2 : qtypCleanUnder res2.regime' qt2 := by
                                    cases hclean with
                                    | clean hpoison_out =>
                                        have henv2 : res2.memEnv'.lookup l ≠ none := by
                                          intro hnone; rw [hlookup2] at hnone; contradiction
                                        rcases
                                            joinMemEnvsStrong_lookup_clean_left
                                              res2.memEnv' res3.memEnv' l qt
                                              hlookup_join hpoison_out henv2
                                          with ⟨qt2', hlookup2', _hetyp2, hpoison2⟩
                                        have hqt2 : qt2 = qt2' := by
                                          rw [hlookup2] at hlookup2'; injection hlookup2'
                                        cases hqt2
                                        exact qtypCleanUnder.clean hpoison2
                                    | guard k htag hk hnotfun =>
                                        have hk_join :
                                            (joinRegimes res2.regime' res3.regime').lookup? k = some true := by
                                          simpa [hregime'] using hk
                                        have htag2 : qtypGuardTag qt2 = some k :=
                                          joinMemEnvsStrong_lookup_guardTag_left
                                            res2.memEnv' res3.memEnv' l qt qt2 k
                                            hlookup_join hlookup2 htag
                                        have hk2 : res2.regime'.lookup? k = some true :=
                                          joinRegimes_lookup_some_left
                                            res2.regime' res3.regime' k true hk_join
                                        have hnotfun2 : qt2.etyp.isFunctionType = false := by
                                          rw [memEnv_lookup_etyp_int res2.memEnv' l qt2 hlookup2]
                                          decide
                                        exact qtypCleanUnder.guard k htag2 hk2 hnotfun2
                                  by_cases hcontains_mid : ctx''.memEnv.contains l
                                  · obtain ⟨qt_mid, hlookup_mid, hclean_mid⟩ :=
                                      typecheckExpr_clean_lookup_origin_of_pc_true
                                        ctx'' e2 fuel' res2 htc2' hwf_ctx'' hbnd_ctx'' hpc''
                                        l qt2 hlookup2 hcontains_mid hclean2
                                    have hθ1_none := _hfresh1 l qt_mid hnotIn
                                      (by simpa [ctx'', ctx', ctxAfter] using hlookup_mid)
                                      (by simpa [ctx'', ctx', ctxAfter] using hclean_mid)
                                    have hpres_loc :=
                                      PreservesInheritedFinalCleanLocsOneRun.apply hpres2
                                        hlookup_mid hlookup2 hclean2
                                    cases hpres_loc with
                                    | both_unrealized _ hout => exact hout
                                    | preserve_value a n hin _ _ _ => simp [hθ1_none] at hin
                                  · exact _hfresh2 l qt2 hcontains_mid hlookup2 hclean2
                                · exact
                                    theta_not_contains_if_not_in_memEnv
                                      (ctxAfter ctx'' res2) cf.memory cf.varEnv θ2 l
                                      hric2 (by simpa [ctxAfter] using hcontains2)
                              have hrd_final : ReservedDiscipline cf.registry res.declared' θ2 := by
                                rw [hdecl']
                                exact ReservedDiscipline.mono_declared
                                  (fun id h => typecheck_declared'_mono _ e3 fuel' res3 htc3' id h)
                                  _hrd2
                              refine ⟨θ2, hθext, ?_, hric_final, hcwr_final, ?_, hpres_final, hfresh_final, hrd_final,
                                hM_case, hF_case⟩
                              · simpa [hetyp] using valueHasETyp_joinETyps_left hv2
                              · refine valueConsistentWithRegimeMasked.noTag ?_ ?_
                                · simp [qtypGuardTag, hpredNo]
                                ·
                                  have hcap2 :
                                      closureCapturedVarsRegimeMasked masked predSat
                                        (ctxAfter ctx'' res2).regime
                                        res2.qualType cf.memory θ2 o :=
                                    valueConsistentWithRegimeMasked_closureCapturedVarsRegime hvalc2
                                  have hlookup_back :
                                      ∀ k b,
                                        (ctxAfter ctxᵢ res).regime.lookup? k = some b →
                                          (ctxAfter ctx'' res2).regime.lookup? k = some b := by
                                    intro k b hk
                                    have hk' :
                                        (joinRegimes res2.regime' res3.regime').lookup? k = some b := by
                                      simpa [ctxAfter, hregime'] using hk
                                    simpa [ctxAfter] using
                                      joinRegimes_lookup_some_left
                                        res2.regime' res3.regime' k b hk'
                                  have hcap2' :
                                      closureCapturedVarsRegimeMasked masked predSat
                                        (ctxAfter ctxᵢ res).regime
                                        res2.qualType cf.memory θ2 o := by
                                    exact
                                      closureCapturedVarsRegimeMasked_transport_lookup_back
                                        (masked := masked) (predSat := predSat)
                                        (R := (ctxAfter ctx'' res2).regime)
                                        (R' := (ctxAfter ctxᵢ res).regime)
                                        (qt := res2.qualType) (μ := cf.memory) (θ := θ2) (v := o)
                                        hlookup_back hcap2
                                  have hcap2_join :
                                      closureCapturedVarsRegimeMasked masked predSat
                                        (ctxAfter ctxᵢ res).regime
                                        ⟨joinETyps res2.qualType.etyp res3.qualType.etyp
                                            res2.qualType.poison res3.qualType.poison,
                                          joinPoison res2.qualType.poison res3.qualType.poison,
                                          joinPredicates res2.qualType.pred res3.qualType.pred⟩
                                        cf.memory θ2 o :=
                                    by
                                      have hcap2'' :
                                          closureCapturedVarsRegimeMasked masked predSat
                                            (ctxAfter ctxᵢ res).regime
                                            ⟨res2.qualType.etyp, res2.qualType.poison, res2.qualType.pred⟩
                                            cf.memory θ2 o := by
                                        cases hq2 : res2.qualType with
                                        | mk etyp2 poison2 pred2 =>
                                            simpa [hq2] using hcap2'
                                      simpa using
                                        (closureCapturedVarsRegimeMasked_joinETyps_step
                                          masked predSat (ctxAfter ctxᵢ res).regime
                                          cf.memory θ2 o
                                          res2.qualType.etyp res3.qualType.etyp
                                          res2.qualType.poison res3.qualType.poison
                                          res2.qualType.pred res3.qualType.pred
                                          hcompat23
                                          hcap2'')
                                  exact
                                    closureCapturedVarsRegimeMasked_transport_etyp
                                      (qt := ⟨joinETyps res2.qualType.etyp res3.qualType.etyp
                                          res2.qualType.poison res3.qualType.poison,
                                        joinPoison res2.qualType.poison res3.qualType.poison,
                                        joinPredicates res2.qualType.pred res3.qualType.pred⟩)
                                      (qt' := res.qualType)
                                      (by simp [hetyp]) hcap2_join
                          | inr hbranch_false =>
                              have ht_e3 : terminatesTo e3 cfg1 cf o := hbranch_false.2
                              have hIH_e3 := IH' fuel' (by omega) tm1 masked e3 ctxForE3
                                hctxStdElse hcan3 res3 htc3'
                              -- Thread extern registry.
                              have hreg_cfg1_std3 : cfg1.registry = registry := by
                                simpa using terminatesTo_preserves_registry ht_e1
                              have hcfg1_eq_std3 : cfg1 = { memory := cfg1.memory, varEnv := cfg1.varEnv, nextAddr := cfg1.nextAddr, pureMode := cfg1.pureMode, registry := registry } :=
                                config_eq_of_registry cfg1 registry hreg_cfg1_std3
                              have hwfcfg1_std3 : wfConfig { memory := cfg1.memory, varEnv := cfg1.varEnv, nextAddr := cfg1.nextAddr, pureMode := cfg1.pureMode, registry := registry } := by
                                rw [← hcfg1_eq_std3]; exact hwfcfg1
                              have ht_e3_std3 : terminatesTo e3 { memory := cfg1.memory, varEnv := cfg1.varEnv, nextAddr := cfg1.nextAddr, pureMode := cfg1.pureMode, registry := registry } cf o := by
                                rw [← hcfg1_eq_std3]; exact ht_e3
                              have hrd_ctxForE3 : ReservedDiscipline registry ctxForE3.declaredExternRefs θ1 := by
                                simp only [ctxForE3]
                                exact ReservedDiscipline.mono_declared
                                  (fun id h => typecheck_declared'_mono _ e2 fuel' res2 htc2' id h)
                                  (by simpa [hreg_cfg1_std3] using! _hrd1)
                              have hroot3std : P ⟨ctxForE3, e3, fuel',
                                  { memory := cfg1.memory, varEnv := cfg1.varEnv, nextAddr := cfg1.nextAddr, pureMode := cfg1.pureMode, registry := registry }⟩ := by
                                rw [← hcfg1_eq_std3]
                                exact hP.closed hroot (SubStep.iteElseStd (f := fuel') hstdArm htc1
                                  (by simpa [hbranch_false.1] using ht_e1) htc2)
                              rcases
                                  (hIH_e3 hpredlaws1 (hframe'.skip hwithin1) hwfTm_ctxForE3
                                    hTmBounded_ctxForE3 hfp_ctxForE3).2
                                    cfg1.memory cfg1.varEnv θ1 cf o
                                    hθ1wf hwf_ctxForE3 hric1_ctxForE3
                                    htagR_ctxForE3 hmasked_none_ctxForE3
                                    hmasked_absent_ctxForE3 hmasked_bounded_ctxForE3 hbnd_ctxForE3 hcwr1_ctxForE3
                                    cfg1.nextAddr cfg1.pureMode hwfcfg1_std3 hres_cfg1 hrd_ctxForE3 ht_e3_std3 hpcForE3
                                    hP hroot3std
                                with ⟨θ3, hθext3, hv3, hric3, hcwr3, hvalc3, hpres3, _hfresh3, _hrd3, hM3, hF3⟩
                              have hθext : wfExtendsMap θ θ3 := wfExtendsMap_trans hθext1 hθext3
                              have hM_case : MapKeepsBelow ctxᵢ.nextLoc θ θ3 := hM1.trans hM3 hnl_else
                              have hF_case : KeepsFootprints tm (ctxAfter ctxᵢ res).regime θ μ cf.memory :=
                                KeepsFootprints.trans hF1 (KeepsFootprints.mono_regime hF3 hRright)
                                  (IsCanonicalExtension.extends_tm hcanon1) hθext1.1 hRback
                              have hcwr3_right :
                                  consistentWithRegimeMasked masked predSat
                                    (ctxAfter ctxᵢ res3).regime
                                    (ctxAfter ctxᵢ res3)
                                    cf.memory cf.varEnv θ3 := by
                                simpa [ctxForE3, ctx'', ctx', pc', ctxAfter, consistentWithRegimeMasked] using hcwr3
                              have hcwr_final :
                                  consistentWithRegimeMasked masked predSat
                                    (ctxAfter ctxᵢ res).regime
                                    (ctxAfter ctxᵢ res)
                                    cf.memory cf.varEnv θ3 := by
                                exact
                                  consistentWithRegimeMasked_join_from_right
                                    masked predSat ctxᵢ
                                    res2 res3 res
                                    cf.memory cf.varEnv θ3
                                    hmemEnv hregime' hcwr3_right
                              have hric_final :
                                  runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf.memory cf.varEnv θ3 := by
                                unfold runtimeInstantiatesCtx at hric3 ⊢
                                constructor
                                · intro l a hθlookup
                                  rcases hric3.1 l a hθlookup with ⟨hcontains3, hmem⟩
                                  rcases
                                      memEnv_lookup_some_of_contains
                                        (ctxAfter ctxForE3 res3).memEnv l hcontains3
                                    with ⟨qt3, hlookup3ctx⟩
                                  have hlookup3 : res3.memEnv'.lookup l = some qt3 := by
                                    simpa [ctxAfter] using hlookup3ctx
                                  rcases
                                      joinMemEnvsStrong_lookup_some_of_right_lookup
                                        res2.memEnv' res3.memEnv' l qt3 hlookup3
                                    with ⟨qt, hlookup_join⟩
                                  have hcontains_join :
                                      (joinMemEnvsStrong res2.memEnv' res3.memEnv').contains l := by
                                    exact
                                      memEnv_contains_of_lookup_some
                                        (joinMemEnvsStrong res2.memEnv' res3.memEnv') l qt hlookup_join
                                  exact ⟨by simpa [ctxAfter, hmemEnv] using hcontains_join, hmem⟩
                                · intro x qt hlookup
                                  have hlookup' :
                                      (ctxAfter ctxForE3 res3).varEnv.lookup x = some qt := by
                                    simpa [ctxAfter, ctxForE3, ctx'', ctx', pc'] using hlookup
                                  exact hric3.2 hlookup'
                              have hpres_branch_final :
                                  PreservesInheritedFinalCleanLocsOneRun
                                    (ctxAfter ctxᵢ res1) res
                                    cfg1.memory cf.memory θ1 θ3 := by
                                refine ⟨?_⟩
                                intro l qt_in qt_out hlookup_in hlookup_out hclean_out
                                have hlookup_join :
                                    (joinMemEnvsStrong res2.memEnv' res3.memEnv').lookup l = some qt_out := by
                                  simpa [hmemEnv] using hlookup_out
                                have hcontains_in :
                                    (ctxAfter ctxᵢ res1).memEnv.contains l := by
                                  exact
                                    memEnv_contains_of_lookup_some
                                      (ctxAfter ctxᵢ res1).memEnv l qt_in
                                      (by simpa [ctxAfter] using hlookup_in)
                                have hcontains3 : res3.memEnv'.contains l :=
                                  typecheckExpr_mem_contains_preserved
                                    ctxForE3 e3 fuel' res3
                                    (by simpa [ctxForE3, ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using! htc3)
                                    l
                                    (by simpa [ctxForE3, ctx'', ctx', pc', ctxAfter] using hcontains_in)
                                rcases memEnv_lookup_some_of_contains res3.memEnv' l hcontains3 with
                                  ⟨qt3, hlookup3⟩
                                have hclean3 : qtypCleanUnder res3.regime' qt3 := by
                                  cases hclean_out with
                                  | clean hpoison_out =>
                                      have henv3 : res3.memEnv'.lookup l ≠ none := by
                                        intro hnone
                                        rw [hlookup3] at hnone
                                        contradiction
                                      rcases
                                          joinMemEnvsStrong_lookup_clean_right
                                            res2.memEnv' res3.memEnv' l qt_out
                                            hlookup_join hpoison_out henv3
                                        with ⟨qt3', hlookup3', _hetyp3, hpoison3⟩
                                      have hqt3 : qt3 = qt3' := by
                                        rw [hlookup3] at hlookup3'
                                        injection hlookup3'
                                      cases hqt3
                                      exact qtypCleanUnder.clean hpoison3
                                  | guard k htag hk hnotfun =>
                                      have hk_join :
                                          (joinRegimes res2.regime' res3.regime').lookup? k = some true := by
                                        simpa [hregime'] using hk
                                      have htag3 : qtypGuardTag qt3 = some k :=
                                        joinMemEnvsStrong_lookup_guardTag_right
                                          res2.memEnv' res3.memEnv' l qt_out qt3 k
                                          hlookup_join hlookup3 htag
                                      have hk3 : res3.regime'.lookup? k = some true :=
                                        joinRegimes_lookup_some_right
                                          res2.regime' res3.regime' k true hk_join
                                      have hnotfun3 : qt3.etyp.isFunctionType = false := by
                                        rw [memEnv_lookup_etyp_int res3.memEnv' l qt3 hlookup3]
                                        decide
                                      exact qtypCleanUnder.guard k htag3 hk3 hnotfun3
                                exact
                                  PreservesInheritedFinalCleanLocsOneRun.apply
                                    (ctx := ctxForE3) (res := res3)
                                    (μ_in := cfg1.memory) (μ_out := cf.memory)
                                    (θ_in := θ1) (θ_out := θ3)
                                    hpres3
                                    (by simpa [ctxForE3, ctx'', ctx', pc', ctxAfter] using hlookup_in)
                                    hlookup3
                                    hclean3
                              have hpres_final :
                                  PreservesInheritedFinalCleanLocsOneRun
                                    ctxᵢ res μ cf.memory θ θ3 := by
                                exact
                                  PreservesInheritedFinalCleanLocsOneRun.compose
                                    (ctx := ctxᵢ) (res1 := res1) (res2 := res)
                                    hclean_back_mid hpres1
                                    (by simpa [ctx'] using hpres_branch_final)
                              have hfresh_final :
                                  FreshCleanLocsUnrealizedOneRun ctxᵢ res θ3 := by
                                intro l qt hnotIn hlookup hclean
                                have hlookup_join :
                                    (joinMemEnvsStrong res2.memEnv' res3.memEnv').lookup l = some qt := by
                                  simpa [hmemEnv] using hlookup
                                by_cases hcontains3 : res3.memEnv'.contains l
                                · rcases memEnv_lookup_some_of_contains res3.memEnv' l hcontains3 with
                                    ⟨qt3, hlookup3⟩
                                  have hclean3 : qtypCleanUnder res3.regime' qt3 := by
                                    cases hclean with
                                    | clean hpoison_out =>
                                        have henv3 : res3.memEnv'.lookup l ≠ none := by
                                          intro hnone; rw [hlookup3] at hnone; contradiction
                                        rcases
                                            joinMemEnvsStrong_lookup_clean_right
                                              res2.memEnv' res3.memEnv' l qt
                                              hlookup_join hpoison_out henv3
                                          with ⟨qt3', hlookup3', _hetyp3, hpoison3⟩
                                        have hqt3 : qt3 = qt3' := by
                                          rw [hlookup3] at hlookup3'; injection hlookup3'
                                        cases hqt3
                                        exact qtypCleanUnder.clean hpoison3
                                    | guard k htag hk hnotfun =>
                                        have hk_join :
                                            (joinRegimes res2.regime' res3.regime').lookup? k = some true := by
                                          simpa [hregime'] using hk
                                        have htag3 : qtypGuardTag qt3 = some k :=
                                          joinMemEnvsStrong_lookup_guardTag_right
                                            res2.memEnv' res3.memEnv' l qt qt3 k
                                            hlookup_join hlookup3 htag
                                        have hk3 : res3.regime'.lookup? k = some true :=
                                          joinRegimes_lookup_some_right
                                            res2.regime' res3.regime' k true hk_join
                                        have hnotfun3 : qt3.etyp.isFunctionType = false := by
                                          rw [memEnv_lookup_etyp_int res3.memEnv' l qt3 hlookup3]
                                          decide
                                        exact qtypCleanUnder.guard k htag3 hk3 hnotfun3
                                  by_cases hcontains_mid : ctxForE3.memEnv.contains l
                                  · obtain ⟨qt_mid, hlookup_mid, hclean_mid⟩ :=
                                      typecheckExpr_clean_lookup_origin_of_pc_true
                                        ctxForE3 e3 fuel' res3 htc3' hwf_ctxForE3 hbnd_ctxForE3 hpcForE3
                                        l qt3 hlookup3 hcontains_mid hclean3
                                    have hθ1_none := _hfresh1 l qt_mid hnotIn
                                      (by simpa [ctxForE3, ctx'', ctx', ctxAfter] using hlookup_mid)
                                      (by simpa [ctxForE3, ctx'', ctx', ctxAfter] using hclean_mid)
                                    have hpres_loc :=
                                      PreservesInheritedFinalCleanLocsOneRun.apply hpres3
                                        hlookup_mid hlookup3 hclean3
                                    cases hpres_loc with
                                    | both_unrealized _ hout => exact hout
                                    | preserve_value a n hin _ _ _ => simp [hθ1_none] at hin
                                  · exact _hfresh3 l qt3 hcontains_mid hlookup3 hclean3
                                · exact
                                    theta_not_contains_if_not_in_memEnv
                                      (ctxAfter ctxForE3 res3) cf.memory cf.varEnv θ3 l
                                      hric3 (by simpa [ctxAfter] using hcontains3)
                              have hrd_final : ReservedDiscipline cf.registry res.declared' θ3 := by
                                rw [hdecl']
                                exact _hrd3
                              refine ⟨θ3, hθext, ?_, hric_final, hcwr_final, ?_, hpres_final, hfresh_final, hrd_final,
                                hM_case, hF_case⟩
                              · simpa [hetyp] using
                                  valueHasETyp_joinETyps_right hcompat23 hv3
                              · refine valueConsistentWithRegimeMasked.noTag ?_ ?_
                                · simp [qtypGuardTag, hpredNo]
                                ·
                                  have hcap3 :
                                      closureCapturedVarsRegimeMasked masked predSat
                                        (ctxAfter ctxForE3 res3).regime
                                        res3.qualType cf.memory θ3 o :=
                                    valueConsistentWithRegimeMasked_closureCapturedVarsRegime hvalc3
                                  have hlookup_back :
                                      ∀ k b,
                                        (ctxAfter ctxᵢ res).regime.lookup? k = some b →
                                          (ctxAfter ctxForE3 res3).regime.lookup? k = some b := by
                                    intro k b hk
                                    have hk' :
                                        (joinRegimes res2.regime' res3.regime').lookup? k = some b := by
                                      simpa [ctxAfter, hregime'] using hk
                                    simpa [ctxAfter] using
                                      joinRegimes_lookup_some_right
                                        res2.regime' res3.regime' k b hk'
                                  have hcap3' :
                                      closureCapturedVarsRegimeMasked masked predSat
                                        (ctxAfter ctxᵢ res).regime
                                        res3.qualType cf.memory θ3 o := by
                                    exact
                                      closureCapturedVarsRegimeMasked_transport_lookup_back
                                        (masked := masked) (predSat := predSat)
                                        (R := (ctxAfter ctxForE3 res3).regime)
                                        (R' := (ctxAfter ctxᵢ res).regime)
                                        (qt := res3.qualType) (μ := cf.memory) (θ := θ3) (v := o)
                                        hlookup_back hcap3
                                  have hcap3_join :
                                      closureCapturedVarsRegimeMasked masked predSat
                                        (ctxAfter ctxᵢ res).regime
                                        ⟨joinETyps res2.qualType.etyp res3.qualType.etyp
                                            res2.qualType.poison res3.qualType.poison,
                                          joinPoison res2.qualType.poison res3.qualType.poison,
                                          joinPredicates res2.qualType.pred res3.qualType.pred⟩
                                        cf.memory θ3 o :=
                                    by
                                      have hcap3'' :
                                          closureCapturedVarsRegimeMasked masked predSat
                                            (ctxAfter ctxᵢ res).regime
                                            ⟨res3.qualType.etyp, res3.qualType.poison, res3.qualType.pred⟩
                                            cf.memory θ3 o := by
                                        cases hq3 : res3.qualType with
                                        | mk etyp3 poison3 pred3 =>
                                            simpa [hq3] using hcap3'
                                      simpa using
                                        (closureCapturedVarsRegimeMasked_joinETyps_step_right
                                          masked predSat (ctxAfter ctxᵢ res).regime
                                          cf.memory θ3 o
                                          res2.qualType.etyp res3.qualType.etyp
                                          res2.qualType.poison res3.qualType.poison
                                          res2.qualType.pred res3.qualType.pred
                                          hcompat23
                                          hcap3'')
                                  exact
                                    closureCapturedVarsRegimeMasked_transport_etyp
                                      (qt := ⟨joinETyps res2.qualType.etyp res3.qualType.etyp
                                          res2.qualType.poison res3.qualType.poison,
                                        joinPoison res2.qualType.poison res3.qualType.poison,
                                        joinPredicates res2.qualType.pred res3.qualType.pred⟩)
                                      (qt' := res.qualType)
                                      (by simp [hetyp]) hcap3_join
