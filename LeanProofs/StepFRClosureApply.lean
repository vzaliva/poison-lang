/-
  App-only closure-application machinery extracted from the `StepFR` hub (refactor T11).

  This module holds `StepFR` lemmas that are consumed only by `StepFRApp` (the function
  application case proof) and have no consumer inside `StepFR` itself. Relocating them here
  shrinks the `StepFR` hub so edits to this machinery no longer trigger rebuilds of the
  other per-operator FR case files, `JoinMemberTransport`, the boundary layer, and the
  orchestration module.

  It imports `StepFR` and is imported only by `StepFRApp`, preserving per-operator
  independence (no sibling `StepFR*` file imports another).
-/
import LeanProofs.StepFR

open List
open List.Mem
open Std
open scoped MemoryTypeEnv

lemma wfValue_mono_of_le_nextAddr {n m : Address} (h : n ≤ m) (x : Name) (v : Value) :
  wfValue n v → wfValue m v := by
  intro hv
  let cfg : Config :=
    { memory := (∅ : Memory), varEnv := [(x, v)], nextAddr := n, pureMode := false}
  have hcfg_n : wfConfig cfg := by
    constructor
    · intro a ha
      simp [cfg] at ha
    · simpa [cfg] using (wfVarEnv.cons x v [] hv wfVarEnv.nil)
  have hcfg_m : wfConfig { cfg with nextAddr := m } := wfConfig_mono cfg m hcfg_n h
  have henv_m : wfVarEnv m [(x, v)] := by
    simpa [cfg] using hcfg_m.2
  cases henv_m with
  | cons _ _ _ hv' _ =>
      simpa using hv'

-- ── Closure-consistency transport / monotonicity leaves (T11, App-only) ──

-- Transport closureCapturedVarsRegime across qt.pred equality.
-- Since the new definition is indexed by qt.etyp, we need an additional
-- etyp equality (defaults to rfl for the common case where only pred changes).
lemma closureCapturedVarsRegime_transport_pred
  {predSat : PredSat} {R : Regime} {qt qt' : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  (h : closureCapturedVarsRegime predSat R qt μ θ v)
  (hetyp : qt.etyp = qt'.etyp := by rfl) :
  closureCapturedVarsRegime predSat R qt' μ θ v :=
  closureCapturedVarsRegime_transport_etyp hetyp h

/-- Extended-regime variant of `valueConsistentWithRegime_monotone`.
    Freshness for the value's own guard tag is discharged from `hqtbound : qtypPredTagBounded qt B`,
    and for the closure-captured tags from `hbound : etypClosuresFullBounded qt.etyp B`. -/
lemma valueConsistentWithRegime_monotoneExt
  {predSat : PredSat} {R R' : Regime} {qt : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  {newTags : Tag → Prop} {B : Tag}
  (h_mono : Regime.monotoneStepExt R R' newTags)
  (hnewB : ∀ k, newTags k → B ≤ k)
  (hqtbound : qtypPredTagBounded qt B)
  (hbound : etypClosuresFullBounded qt.etyp B)
  (h : valueConsistentWithRegime predSat R qt μ θ v) :
  valueConsistentWithRegime predSat R' qt μ θ v := by
  cases h with
  | noTag htag hcap =>
      exact valueConsistentWithRegime.noTag htag
        (closureCapturedVarsRegime_monotoneExt h_mono hnewB hbound hcap)
  | guardOnly_ok k hgo hcap =>
      exact valueConsistentWithRegime.guardOnly_ok k hgo
        (closureCapturedVarsRegime_monotoneExt h_mono hnewB hbound hcap)
  | notInRegime k htag hknone hcap =>
      have h' : R'.lookup? k = none := by
        by_contra hneq
        rcases h_mono.2 k hneq with hRne | hnew
        · exact hRne hknone
        · exact absurd (hnewB k hnew)
            (Nat.not_le.2 (qtypGuardTag_lt_of_predTagBounded hqtbound htag))
      exact valueConsistentWithRegime.notInRegime k htag h'
        (closureCapturedVarsRegime_monotoneExt h_mono hnewB hbound hcap)
  | inRegimeTrue k htag hktrue hholds hcap =>
      have hcap' := closureCapturedVarsRegime_monotoneExt h_mono hnewB hbound hcap
      have hknew : ¬ newTags k := fun hnt =>
        absurd (hnewB k hnt) (Nat.not_le.2 (qtypGuardTag_lt_of_predTagBounded hqtbound htag))
      cases h_mono.1 k true hknew hktrue with
      | inl hk' => exact valueConsistentWithRegime.inRegimeTrue k htag hk' hholds hcap'
      | inr hk'none => exact valueConsistentWithRegime.notInRegime k htag hk'none hcap'
  | inRegimeFalse k htag hkfalse hnot hcap =>
      have hcap' := closureCapturedVarsRegime_monotoneExt h_mono hnewB hbound hcap
      have hknew : ¬ newTags k := fun hnt =>
        absurd (hnewB k hnt) (Nat.not_le.2 (qtypGuardTag_lt_of_predTagBounded hqtbound htag))
      cases h_mono.1 k false hknew hkfalse with
      | inl hk' => exact valueConsistentWithRegime.inRegimeFalse k htag hk' hnot hcap'
      | inr hk'none => exact valueConsistentWithRegime.notInRegime k htag hk'none hcap'

-- Build a `varsRegime` fact for an active-guard variable from the corresponding
-- `valueConsistentWithRegime` fact.
lemma varsRegime_of_valueConsistentWithRegime_active
  {predSat : PredSat} {R : Regime} {μ : Memory} {θ : RealizationMap} {ρ : VarEnv}
  {x : Name} {qt : QTyp} {v : Value} {k : Tag}
  (hlookup : ρ.lookup x = some v)
  (hguard : qtypGuardTag qt = some k)
  (hRdef : R.lookup? k ≠ none)
  (hvalc : valueConsistentWithRegime predSat R qt μ θ v) :
  varsRegime predSat R μ ρ (x, qt) := by
  cases hpred : qt.pred with
  | noPred =>
      simp [qtypGuardTag, hpred] at hguard
  | guardOnly k0 =>
      exact varsRegime.guardOnly_ok (x, qt) k0 hpred
  | guardClosure k0 arg_name pred_body var_env =>
      have hk0_ne : R.lookup? k0 ≠ none := by
        have htag0 : qtypGuardTag qt = some k0 := by
          simp [qtypGuardTag, hpred]
        have hk_eq : k0 = k := by
          have : some k0 = some k := by
            calc
              some k0 = qtypGuardTag qt := by symm; exact htag0
              _ = some k := hguard
          exact Option.some.inj this
        simpa [hk_eq] using hRdef
      cases hlookupR : R.lookup? k0 with
      | none =>
          exact (hk0_ne hlookupR).elim
      | some b =>
          have hcons :
              (b = true → qtypPredHolds predSat qt μ v) ∧
              (b = false → ¬ qtypPredHolds predSat qt μ v) :=
            valueConsistentWithRegime_guardClosure_consistency
              (predSat := predSat) (R := R) (qt := qt) (μ := μ) (v := v)
              (k := k0) (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
              (b := b) hvalc hpred hlookupR
          exact varsRegime.withPred_ok (x, qt) k0 arg_name pred_body var_env v b hpred hlookupR hlookup hcons

lemma closureCapturedVarsRegimeMasked_transport_pred
  {masked : Tag → Prop} {predSat : PredSat} {R : Regime}
  {qt qt' : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  (h : closureCapturedVarsRegimeMasked masked predSat R qt μ θ v)
  (hetyp : qt.etyp = qt'.etyp := by rfl) :
  closureCapturedVarsRegimeMasked masked predSat R qt' μ θ v :=
  closureCapturedVarsRegimeMasked_transport_etyp hetyp h

private lemma agreeCapturedEnv_lookup_agreeVarUnder_clean
  {predSat : PredSat} {R : Regime}
  {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
  {σcap : CapturedVarEnv} {ρcap₀ ρcap₁ : VarEnv}
  {x : Name} {qt : QTyp}
  (hcap : agreeCapturedEnv predSat R μ₀ μ₁ θ₀ θ₁ σcap ρcap₀ ρcap₁)
  (hlookup : σcap.lookup x = some qt)
  (hclean : qtypCleanUnder R qt) :
  agreeVarUnder predSat R μ₀ ρcap₀ μ₁ ρcap₁ θ₀ θ₁ (x, qt) := by
  revert x qt hlookup hclean
  induction σcap generalizing ρcap₀ ρcap₁ with
  | nil =>
      intro x qt hlookup hclean
      cases hcap with
      | nil =>
          simp [CapturedVarEnv.lookup_eq, List.lookup] at hlookup
  | cons entry σtail ih =>
      intro x qt hlookup hclean
      rcases entry with ⟨xh, qtHead⟩
      cases hcap with
      | cons_clean hclean_head hlookup₀ hlookup₁ htyp₀ htyp₁ hagree_head htail =>
          by_cases hxx : x == xh
          · simp [CapturedVarEnv.lookup_eq, List.lookup, hxx] at hlookup
            have hxx' : x = xh := beq_iff_eq.mp hxx
            subst hxx'
            cases hlookup
            exact agreeVarUnder.agree_values _ _ _ _ hlookup₀ hlookup₁ hagree_head
          · simp [CapturedVarEnv.lookup_eq, List.lookup, hxx] at hlookup
            exact ih (hcap := htail) hlookup hclean
      | cons_dirty hdirty_head hlookup₀ hlookup₁ htyp₀ htyp₁ htail =>
          by_cases hxx : x == xh
          · simp [CapturedVarEnv.lookup_eq, List.lookup, hxx] at hlookup
            have hxx' : x = xh := beq_iff_eq.mp hxx
            subst hxx'
            cases hlookup
            exact (hdirty_head hclean).elim
          · simp [CapturedVarEnv.lookup_eq, List.lookup, hxx] at hlookup
            exact ih (hcap := htail) hlookup hclean

lemma agreeOnClean_closure_body_start
  (predSat : PredSat)
  (ctx : TypeContext) (result1 : TypeResult)
  (σcap : CapturedVarEnv) (xArg : Name) (argQt : QTyp)
  (μ₀ μ₁ : Memory) (θ₀ θ₁ : RealizationMap)
  (ρcap₀ ρcap₁ : VarEnv) (vArg₀ vArg₁ : Value)
  (hmem_agree :
    ∀ l qt,
      result1.memEnv'.lookup l = some qt →
      qtypCleanUnder result1.regime' qt →
      agreeLocUnder predSat result1.regime' μ₀ μ₁ θ₀ θ₁ (l, qt))
  (hcap :
    agreeCapturedEnv predSat result1.regime' μ₀ μ₁ θ₀ θ₁ σcap ρcap₀ ρcap₁)
  (harg_agree :
    qtypCleanUnder result1.regime' argQt →
      agreeValueUnder predSat result1.regime' μ₀ μ₁ θ₀ θ₁ argQt vArg₀ vArg₁) :
  let bodyCtx : TypeContext :=
    { ctx with
      memEnv := result1.memEnv'
      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) xArg argQt
      tagEnv := result1.tagEnv'
      nextTag := result1.nextTag'
      nextLoc := result1.nextLoc'
      regime := result1.regime' }
  agreeOnClean predSat bodyCtx.regime bodyCtx
    μ₀ (VarEnv.update ρcap₀ xArg vArg₀) θ₀
    μ₁ (VarEnv.update ρcap₁ xArg vArg₁) θ₁ := by
  intro bodyCtx
  constructor
  · intro l qt hlookup hclean
    exact hmem_agree l qt (by simpa [bodyCtx] using hlookup) (by simpa [bodyCtx] using hclean)
  · intro x qt hlookup hclean
    by_cases hx : x = xArg
    · have hlookup_xarg :
          (VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) xArg argQt).lookup xArg = some qt := by
        simpa [bodyCtx, hx] using hlookup
      have hqt : qt = argQt := by
        have hself :
            (VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) xArg argQt).lookup xArg = some argQt :=
          VarTypeEnv_lookup_update_eq (VarTypeEnv.ofCaptured σcap) xArg argQt
        have : (some qt : Option QTyp) = some argQt := by
          calc
            some qt =
                (VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) xArg argQt).lookup xArg := by
                  symm
                  exact hlookup_xarg
            _ = some argQt := hself
        exact Option.some.inj this
      have hlookup₀ : (VarEnv.update ρcap₀ xArg vArg₀).lookup x = some vArg₀ := by
        simp [hx, VarEnv.update, VarEnv.lookup]
      have hlookup₁ : (VarEnv.update ρcap₁ xArg vArg₁).lookup x = some vArg₁ := by
        simp [hx, VarEnv.update, VarEnv.lookup]
      have hclean_arg : qtypCleanUnder result1.regime' argQt := by
        simpa [bodyCtx, hx, hqt] using hclean
      exact agreeVarUnder.agree_values x qt vArg₀ vArg₁ hlookup₀ hlookup₁
        (by simpa [hqt] using (harg_agree hclean_arg))
    · have hlookupCap : σcap.lookup x = some qt := by
        have hlookupCap' : (VarTypeEnv.ofCaptured σcap).lookup x = some qt := by
          have hne_lookup :
              (VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) xArg argQt).lookup x =
                (VarTypeEnv.ofCaptured σcap).lookup x :=
            VarTypeEnv_lookup_update_ne (VarTypeEnv.ofCaptured σcap) xArg x argQt hx
          simpa [bodyCtx, hne_lookup] using hlookup
        exact list_lookup_of_ofCaptured_lookup σcap x qt hlookupCap'
      have hcapAgree :
          agreeVarUnder predSat result1.regime' μ₀ ρcap₀ μ₁ ρcap₁ θ₀ θ₁ (x, qt) :=
        agreeCapturedEnv_lookup_agreeVarUnder_clean
          (hcap := hcap) (hlookup := hlookupCap) (hclean := hclean)
      cases hcapAgree with
      | agree_values _ _ v₀ v₁ hlookup₀ hlookup₁ hagree =>
          have hlookup₀' : (VarEnv.update ρcap₀ xArg vArg₀).lookup x = some v₀ := by
            have hne :=
              VarEnv_lookup_update_ne ρcap₀ xArg x vArg₀ hx
            simpa [hne] using hlookup₀
          have hlookup₁' : (VarEnv.update ρcap₁ xArg vArg₁).lookup x = some v₁ := by
            have hne :=
              VarEnv_lookup_update_ne ρcap₁ xArg x vArg₁ hx
            simpa [hne] using hlookup₁
          exact agreeVarUnder.agree_values _ _ _ _ hlookup₀' hlookup₁' hagree
      | both_none _ _ hnone₀ hnone₁ =>
          have hnone₀' : (VarEnv.update ρcap₀ xArg vArg₀).lookup x = none := by
            have hne :=
              VarEnv_lookup_update_ne ρcap₀ xArg x vArg₀ hx
            simpa [hne] using hnone₀
          have hnone₁' : (VarEnv.update ρcap₁ xArg vArg₁).lookup x = none := by
            have hne :=
              VarEnv_lookup_update_ne ρcap₁ xArg x vArg₁ hx
            simpa [hne] using hnone₁
          exact agreeVarUnder.both_none _ _ hnone₀' hnone₁'

lemma consistentWithRegime_closure_body_start
  (predSat : PredSat)
  (ctx : TypeContext) (result1 : TypeResult)
  (σcap : CapturedVarEnv) (xArg : Name) (argQt : QTyp)
  (μ : Memory) (θ : RealizationMap) (ρcap : VarEnv) (vArg : Value)
  (hlocs_src :
    ∀ l qt k,
      result1.memEnv'.lookup l = some qt →
      qtypGuardTag qt = some k →
      result1.regime'.lookup? k ≠ none →
      locsRegime predSat result1.regime' μ θ (l, qt))
  (hvars_cap :
    ∀ x qt k,
      (VarTypeEnv.ofCaptured σcap).lookup x = some qt →
      qtypGuardTag qt = some k →
      result1.regime'.lookup? k ≠ none →
      varsRegime predSat result1.regime' μ ρcap (x, qt))
  (hvars_arg :
    ∀ k,
      qtypGuardTag argQt = some k →
      result1.regime'.lookup? k ≠ none →
      varsRegime predSat result1.regime' μ (VarEnv.update ρcap xArg vArg) (xArg, argQt))
  (h_cap_cvcr :
    ∀ x qt v,
      (VarTypeEnv.ofCaptured σcap).lookup x = some qt →
      ρcap.lookup x = some v →
      closureCapturedVarsRegime predSat result1.regime' qt μ θ v)
  (h_arg_cvcr :
    closureCapturedVarsRegime predSat result1.regime' argQt μ θ vArg) :
  let bodyCtx : TypeContext :=
    { ctx with
      memEnv := result1.memEnv'
      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) xArg argQt
      tagEnv := result1.tagEnv'
      nextTag := result1.nextTag'
      nextLoc := result1.nextLoc'
      regime := result1.regime' }
  consistentWithRegime predSat bodyCtx.regime bodyCtx μ (VarEnv.update ρcap xArg vArg) θ := by
  intro bodyCtx
  refine ⟨?_, ?_, ?_⟩
  · intro l qt k hlookup hguard hRdef
    exact hlocs_src l qt k (by simpa [bodyCtx] using hlookup) (by simpa [bodyCtx] using hguard)
      (by simpa [bodyCtx] using hRdef)
  · intro x qt k hlookup hguard hRdef
    by_cases hx : x = xArg
    · have hlookup_xarg :
          (VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) xArg argQt).lookup xArg = some qt := by
        simpa [bodyCtx, hx] using hlookup
      have hqt : qt = argQt := by
        have hself :
            (VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) xArg argQt).lookup xArg = some argQt :=
          VarTypeEnv_lookup_update_eq (VarTypeEnv.ofCaptured σcap) xArg argQt
        have : (some qt : Option QTyp) = some argQt := by
          calc
            some qt =
                (VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) xArg argQt).lookup xArg := by
                  symm
                  exact hlookup_xarg
            _ = some argQt := hself
        exact Option.some.inj this
      subst hqt
      have hRdef' : result1.regime'.lookup? k ≠ none := by
        simpa [bodyCtx] using hRdef
      simpa [bodyCtx, hx] using (hvars_arg k hguard hRdef')
    · have hlookup_cap : (VarTypeEnv.ofCaptured σcap).lookup x = some qt := by
        have hne_lookup :
            (VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) xArg argQt).lookup x =
              (VarTypeEnv.ofCaptured σcap).lookup x :=
          VarTypeEnv_lookup_update_ne (VarTypeEnv.ofCaptured σcap) xArg x argQt hx
        simpa [bodyCtx, hne_lookup] using hlookup
      have hvars := hvars_cap x qt k hlookup_cap hguard (by simpa [bodyCtx] using hRdef)
      cases hvars with
      | noPred_ok hnp =>
          exact varsRegime.noPred_ok (x, qt) hnp
      | guardOnly_ok k' hgo =>
          exact varsRegime.guardOnly_ok (x, qt) k' hgo
      | withPred_ok k' arg_name pred_body var_env v b hclos hreg hvar hcons =>
          have hvar' : (VarEnv.update ρcap xArg vArg).lookup x = some v := by
            have hne := VarEnv_lookup_update_ne ρcap xArg x vArg hx
            simpa [hne] using hvar
          exact varsRegime.withPred_ok (x, qt) k' arg_name pred_body var_env v b hclos hreg hvar' hcons
  · intro x qt v hlookup hlookup_v
    by_cases hx : x = xArg
    · have hlookup_xarg :
          (VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) xArg argQt).lookup xArg = some qt := by
        simpa [bodyCtx, hx] using hlookup
      have hqt : qt = argQt := by
        have hself :
            (VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) xArg argQt).lookup xArg = some argQt :=
          VarTypeEnv_lookup_update_eq (VarTypeEnv.ofCaptured σcap) xArg argQt
        have : (some qt : Option QTyp) = some argQt := by
          calc
            some qt =
                (VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) xArg argQt).lookup xArg := by
                  symm
                  exact hlookup_xarg
            _ = some argQt := hself
        exact Option.some.inj this
      subst hqt
      have hv : v = vArg := by
        have hself : (VarEnv.update ρcap xArg vArg).lookup xArg = some vArg := by
          simp [VarEnv.update, VarEnv.lookup]
        have hlookup_v_xarg : (VarEnv.update ρcap xArg vArg).lookup xArg = some v := by
          simpa [hx, VarEnv.update, VarEnv.lookup] using hlookup_v
        exact Option.some.inj (hlookup_v_xarg.symm.trans hself)
      subst hv
      exact h_arg_cvcr
    · have hlookup_cap : (VarTypeEnv.ofCaptured σcap).lookup x = some qt := by
        have hne_lookup :
            (VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) xArg argQt).lookup x =
              (VarTypeEnv.ofCaptured σcap).lookup x :=
          VarTypeEnv_lookup_update_ne (VarTypeEnv.ofCaptured σcap) xArg x argQt hx
        simpa [bodyCtx, hne_lookup] using hlookup
      have hlookup_v_cap : ρcap.lookup x = some v := by
        have hne := VarEnv_lookup_update_ne ρcap xArg x vArg hx
        simpa [hne] using hlookup_v
      exact h_cap_cvcr x qt v hlookup_cap hlookup_v_cap

lemma valueConsistentWithRegimeMasked_monotoneExt
  {masked : Tag → Prop} {predSat : PredSat} {R R' : Regime}
  {qt : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value} {newTags : Tag → Prop} {B : Tag}
  (h_mono : Regime.monotoneStepExt R R' newTags) (hnewB : ∀ k, newTags k → B ≤ k)
  (hqtbound : qtypPredTagBounded qt B) (hbound : etypClosuresFullBounded qt.etyp B)
  (h : valueConsistentWithRegimeMasked masked predSat R qt μ θ v) :
  valueConsistentWithRegimeMasked masked predSat R' qt μ θ v := by
  cases h with
  | noTag htag hcap =>
      exact valueConsistentWithRegimeMasked.noTag htag
        (closureCapturedVarsRegimeMasked_monotoneExt h_mono hnewB hbound hcap)
  | guardOnly_ok k hgo hcap =>
      exact valueConsistentWithRegimeMasked.guardOnly_ok k hgo
        (closureCapturedVarsRegimeMasked_monotoneExt h_mono hnewB hbound hcap)
  | maskedTag k htag hmasked hcap =>
      exact valueConsistentWithRegimeMasked.maskedTag k htag hmasked
        (closureCapturedVarsRegimeMasked_monotoneExt h_mono hnewB hbound hcap)
  | notInRegime k htag hknone hcap =>
      have h' : R'.lookup? k = none := by
        by_contra hneq
        rcases h_mono.2 k hneq with hRne | hnew
        · exact hRne hknone
        · exact absurd (hnewB k hnew)
            (Nat.not_le.2 (qtypGuardTag_lt_of_predTagBounded hqtbound htag))
      exact valueConsistentWithRegimeMasked.notInRegime k htag h'
        (closureCapturedVarsRegimeMasked_monotoneExt h_mono hnewB hbound hcap)
  | inRegimeTrue k htag hktrue hholds hcap =>
      have hcap' := closureCapturedVarsRegimeMasked_monotoneExt h_mono hnewB hbound hcap
      have hknew : ¬ newTags k := fun hnt =>
        absurd (hnewB k hnt) (Nat.not_le.2 (qtypGuardTag_lt_of_predTagBounded hqtbound htag))
      cases h_mono.1 k true hknew hktrue with
      | inl hk' => exact valueConsistentWithRegimeMasked.inRegimeTrue k htag hk' hholds hcap'
      | inr hk'none => exact valueConsistentWithRegimeMasked.notInRegime k htag hk'none hcap'
  | inRegimeFalse k htag hkfalse hnot hcap =>
      have hcap' := closureCapturedVarsRegimeMasked_monotoneExt h_mono hnewB hbound hcap
      have hknew : ¬ newTags k := fun hnt =>
        absurd (hnewB k hnt) (Nat.not_le.2 (qtypGuardTag_lt_of_predTagBounded hqtbound htag))
      cases h_mono.1 k false hknew hkfalse with
      | inl hk' => exact valueConsistentWithRegimeMasked.inRegimeFalse k htag hk' hnot hcap'
      | inr hk'none => exact valueConsistentWithRegimeMasked.notInRegime k htag hk'none hcap'
