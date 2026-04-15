/-
  StepFRAssign.lean - Fault-robustness proof for assignment (stepFR_assign).

  Contains the stepFR_assign lemma and all helper lemmas used exclusively by it,
  including invalidateRegimeDeps infrastructure, assign memory formula helpers,
  PredRespectsTagMeaning, and EnvRespectsTagMeaning update lemmas.
-/
import LeanProofs.StepFR

open List
open List.Mem
open Std
open scoped MemoryTypeEnv

private def StepFRSingleRunFinalCleanPcTrueWithCtxValCons
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
  
  (ctx : TypeContext)
  (e : Expr)
  (res : TypeResult)
  (predSat : PredSat)
  (tm : TagMeaning) : Prop :=
    PredSatLaws predSat tm →
    wfTagMeaningCtx tm ctx →
    ∀ (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
      (cf : Config) (o : Value),
      wfRealizationMap θ →
      wfTypeContext ctx →
      runtimeInstantiatesCtx ctx μ ρ θ →
      regimeConsistentWithCtx ctx →
      CtxCons ctx μ ρ θ →
      ∀ (a : Address) (pm : Bool),
        wfConfig { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } →
        terminatesTo e { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o →
        ctx.pc = true →
        ∃ (θ' : RealizationMap),
          wfExtendsMap θ θ' ∧
          valueHasETyp θ' o res.qualType.etyp ∧
          runtimeInstantiatesCtx (ctxAfter ctx res) cf.memory cf.varEnv θ' ∧
          CtxCons (ctxAfter ctx res) cf.memory cf.varEnv θ' ∧
          ValCons (ctxAfter ctx res).regime res.qualType cf.memory θ' o ∧
          PreservesInheritedFinalCleanLocsOneRun ctx res μ cf.memory θ θ' ∧
          FreshCleanLocsUnrealizedOneRun ctx res θ'

private abbrev StepFRSingleRunFinalCleanPcTrueWithCtxValCons_IH
    (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
    (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
    (predSat : PredSat) (tm : TagMeaning) (fuel : Nat) : Prop :=
  ∀ m < fuel, ∀ (e : Expr) (ctx : TypeContext),
    wfTagMeaningCtx tm ctx →
    ∀ (res : TypeResult),
      typecheck ctx e m = .ok res →
      StepFRSingleRunFinalCleanPcTrueWithCtxValCons
        CtxCons ValCons ctx e res predSat tm

private def AssignCtxConsPostTransport
  (RegCtx : TypeContext → Prop)
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (predSat : PredSat) (tm : TagMeaning) : Prop :=
  ∀ (ctx : TypeContext)
    (result1 result2 res : TypeResult) (ls : LocSet)
    (cfg2 cf : Config) (θ : RealizationMap) (a_w : Address) (n : Int),
    PredSatLaws predSat tm →
    wfTagMeaningCtx tm (ctxAfter (ctxAfter ctx result1) result2) →
    wfTypeContext (ctxAfter (ctxAfter ctx result1) result2) →
    runtimeInstantiatesCtx (ctxAfter (ctxAfter ctx result1) result2) cfg2.memory cfg2.varEnv θ →
    RegCtx (ctxAfter (ctxAfter ctx result1) result2) →
    CtxCons (ctxAfter (ctxAfter ctx result1) result2) cfg2.memory cfg2.varEnv θ →
    result1.qualType.etyp = ETyp.ref ls →
    valueHasETyp θ (Value.loc a_w) result1.qualType.etyp →
    wfRealizationMap θ →
    cf.memory = Std.ExtTreeMap.insert cfg2.memory a_w n →
    cf.varEnv = cfg2.varEnv →
    res.nextLoc' = ls.fold result2.nextLoc' (fun acc l => max acc (l + 1)) →
    res.nextTag' = result2.nextTag' →
    res.regime' = invalidateRegimeDeps result2.regime' result2.tagEnv' ls →
    (res.memEnv' =
      match Std.ExtTreeSet.toList ls with
      | [l] =>
          updateMemEnv result2.memEnv' l
            { etyp := ETyp.int
              poison := joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison)
              pred := if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred }
      | _ =>
          updateLocsetWeak result2.memEnv' ls
            (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
            (if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred)) →
    res.tagEnv' = invalidateTagDeps result2.tagEnv' ls →
    ctx.pc = true →
    wfTagMeaningCtx tm (ctxAfter ctx res) ∧
    wfTypeContext (ctxAfter ctx res) ∧
    runtimeInstantiatesCtx (ctxAfter ctx res) cf.memory cf.varEnv θ ∧
    RegCtx (ctxAfter ctx res) ∧
    CtxCons (ctxAfter ctx res) cf.memory cf.varEnv θ

private def AssignResultValCons
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop) : Prop :=
  ∀ (ctx : TypeContext) (res : TypeResult) (cf : Config)
    (θ : RealizationMap),
    res.qualType.pred = Predicate.noPred →
    res.qualType.etyp = ETyp.unit →
    ValCons (ctxAfter ctx res).regime res.qualType cf.memory θ Value.unit

private lemma invalidateRegimeDeps_preserves_lookup_of_surviving_tag
    (R : Regime) (env : TagEnv) (ls : LocSet) (k : Tag) (b : Bool)
    (hR : R.lookup? k = some b)
    (hkeep : (invalidateTagDeps env ls).contains k = true) :
    (invalidateRegimeDeps R env ls).lookup? k = some b := by
  unfold Regime.lookup? at hR ⊢
  unfold invalidateRegimeDeps
  unfold invalidateTagDeps at hkeep
  have hmap' :
      (R.filter (fun k _ => (env.filter (fun _ tv => !tv.deps.any ls.contains)).contains k)).get? k = some b := by
    rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_filter']
    rw [← Std.ExtTreeMap.get?_eq_getElem?, hR]
    simp [hkeep]
  simpa [Regime.lookup?] using hmap'

private lemma invalidateTagDeps_contains_true_implies_lookup_some_and_disjoint
    (env : TagEnv) (ls : LocSet) (k : Tag)
    (hkeep : (invalidateTagDeps env ls).contains k = true) :
    ∃ tv, env.get? k = some tv ∧ tv.deps.any ls.contains = false := by
  unfold invalidateTagDeps at hkeep
  rw [Std.ExtTreeMap.contains_eq_isSome_getElem?] at hkeep
  have hsome : ((env.filter (fun _ tv => !tv.deps.any ls.contains))[k]?).isSome = true := by
    simpa using hkeep
  rw [Std.ExtTreeMap.getElem?_filter'] at hsome
  cases hget : env[k]? with
  | none =>
      simp [hget] at hsome
  | some tv =>
      have hdeps : tv.deps.any ls.contains = false := by
        cases hdep : tv.deps.any ls.contains with
        | false =>
            rfl
        | true =>
            simp [hget, hdep] at hsome
      refine ⟨tv, ?_, hdeps⟩
      simpa [Std.ExtTreeMap.get?_eq_getElem?] using hget

private lemma invalidateRegimeDeps_lookup_eq_lookup_of_surviving_tag
    (R : Regime) (env : TagEnv) (ls : LocSet) (k : Tag)
    (hkeep : (invalidateTagDeps env ls).contains k = true) :
    (invalidateRegimeDeps R env ls).lookup? k = R.lookup? k := by
  cases hR : R.lookup? k with
  | none =>
      unfold invalidateRegimeDeps Regime.lookup? at ⊢
      unfold Regime.lookup? at hR
      have hmapNone : R.get? k = none := hR
      have : (R.filter (fun k _ => (invalidateTagDeps env ls).contains k)).get? k = none := by
        rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_filter']
        rw [← Std.ExtTreeMap.get?_eq_getElem?, hmapNone]
        simp
      exact this
  | some b =>
      have hkeepLookup :
          (invalidateRegimeDeps R env ls).lookup? k = some b :=
        invalidateRegimeDeps_preserves_lookup_of_surviving_tag R env ls k b hR hkeep
      simpa [hR] using hkeepLookup

private lemma invalidateRegimeDeps_survives_of_lookup_ne_none
    (R : Regime) (env : TagEnv) (ls : LocSet) (k : Tag)
    (hlookup : (invalidateRegimeDeps R env ls).lookup? k ≠ none) :
    (invalidateTagDeps env ls).contains k = true := by
  unfold invalidateRegimeDeps Regime.lookup? at hlookup
  have hmap : (R.filter (fun k _ => (invalidateTagDeps env ls).contains k)).get? k ≠ none := by
    simpa using hlookup
  by_contra hkeep
  have hmapEq :
      (R.filter (fun k _ => (invalidateTagDeps env ls).contains k)).get? k =
        Option.filter (fun _ => (invalidateTagDeps env ls).contains k) (R.get? k) := by
    rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_filter']
    rw [← Std.ExtTreeMap.get?_eq_getElem?]
  have : (R.filter (fun k _ => (invalidateTagDeps env ls).contains k)).get? k = none := by
    rw [hmapEq]
    simp [hkeep]
  exact hmap this

private lemma invalidateRegimeDeps_lookup_ne_none_implies_original_ne_none
    (R : Regime) (env : TagEnv) (ls : LocSet) (k : Tag)
    (hlookup : (invalidateRegimeDeps R env ls).lookup? k ≠ none) :
    R.lookup? k ≠ none := by
  have hkeep : (invalidateTagDeps env ls).contains k = true :=
    invalidateRegimeDeps_survives_of_lookup_ne_none R env ls k hlookup
  have heq :
      (invalidateRegimeDeps R env ls).lookup? k = R.lookup? k :=
    invalidateRegimeDeps_lookup_eq_lookup_of_surviving_tag R env ls k hkeep
  rwa [heq] at hlookup

private lemma invalidateRegimeDeps_lookup_ne_none_implies_surviving_tag_entry
    (R : Regime) (env : TagEnv) (ls : LocSet) (k : Tag)
    (hlookup : (invalidateRegimeDeps R env ls).lookup? k ≠ none) :
    ∃ tv, env.get? k = some tv ∧ tv.deps.any ls.contains = false := by
  have hkeep : (invalidateTagDeps env ls).contains k = true :=
    invalidateRegimeDeps_survives_of_lookup_ne_none R env ls k hlookup
  exact invalidateTagDeps_contains_true_implies_lookup_some_and_disjoint env ls k hkeep

private lemma regime_lookup_ne_none_or_false_tag_of_invalidate_lookup
    (R R2 : Regime) (env : TagEnv) (ls : LocSet) (k : Tag)
    (hcons : tagEnvConsistentWithRegime env R2)
    (hlookup : (invalidateRegimeDeps R env ls).lookup? k ≠ none) :
    R2.lookup? k ≠ none ∨ ∃ deps, env.get? k = some ⟨false, deps⟩ := by
  rcases invalidateRegimeDeps_lookup_ne_none_implies_surviving_tag_entry R env ls k hlookup with
    ⟨⟨b, deps⟩, hget, _hdeps⟩
  cases hb : b with
  | true =>
      left
      have hktrue : R2.lookup? k = some true := hcons k deps (by simp [hb] at hget; exact hget)
      simp [hktrue]
  | false =>
      right
      exact ⟨deps, by simp [hb] at hget; exact hget⟩

private lemma qtypCleanUnder_of_monotone
    {R R' : Regime} (hmono : Regime.monotoneStep R R') {qt : QTyp} :
    qtypCleanUnder R' qt → qtypCleanUnder R qt := by
  intro hclean
  cases hclean with
  | clean hpoison =>
      exact qtypCleanUnder.clean hpoison
  | guard k htag hreg hnotfun =>
      have hkR : R.lookup? k ≠ none := hmono.2 k (by simp [hreg])
      cases hk : R.lookup? k with
      | none =>
          exact (hkR hk).elim
      | some b =>
          have hcases : R'.lookup? k = some b ∨ R'.lookup? k = none := hmono.1 k b hk
          cases hcases with
          | inl hk' =>
              have hb : b = true := by
                have : some b = some true := by
                  simpa [hk'] using hreg
                exact Option.some.inj this
              subst hb
              exact qtypCleanUnder.guard k htag hk hnotfun
          | inr hkNone =>
              simp [hkNone] at hreg

private lemma qtypCleanUnder_of_invalidateRegimeDeps
    (R : Regime) (env : TagEnv) (ls : LocSet) {qt : QTyp}
    (hclean : qtypCleanUnder (invalidateRegimeDeps R env ls) qt) :
    qtypCleanUnder R qt := by
  cases hclean with
  | clean hpoison =>
      exact qtypCleanUnder.clean hpoison
  | guard k htag hreg hnotfun =>
      have hlookup_inv : (invalidateRegimeDeps R env ls).lookup? k ≠ none := by
        simp [hreg]
      have hkeep : (invalidateTagDeps env ls).contains k = true :=
        invalidateRegimeDeps_survives_of_lookup_ne_none R env ls k hlookup_inv
      have heq :
          (invalidateRegimeDeps R env ls).lookup? k = R.lookup? k :=
        invalidateRegimeDeps_lookup_eq_lookup_of_surviving_tag R env ls k hkeep
      have hregR : R.lookup? k = some true := by
        simpa [heq] using hreg
      exact qtypCleanUnder.guard k htag hregR hnotfun

private lemma agreeValueUnder_transport_memory
    {predSat : PredSat} {R : Regime}
    {μ₀ μ₁ μ₀' μ₁' : Memory}
    {θ₀ θ₁ : RealizationMap} {qt : QTyp} {v₀ v₁ : Value}
    (_hpred_compat₀ : ∀ (qt : QTyp) (v : Value),
      qtypPredHolds predSat qt μ₀ v ↔ qtypPredHolds predSat qt μ₀' v)
    (_hpred_compat₁ : ∀ (qt : QTyp) (v : Value),
      qtypPredHolds predSat qt μ₁ v ↔ qtypPredHolds predSat qt μ₁' v)
    (hclean : qtypCleanUnder R qt) :
    agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ →
    agreeValueUnder predSat R μ₀' μ₁' θ₀ θ₁ qt v₀ v₁ := by
  intro hagree
  exact
    agreeValueUnder_clean_extends_transport_mem _hpred_compat₀ _hpred_compat₁
      hclean
      (by intro l a h; exact h)
      (by intro l a h; exact h)
      hagree

private lemma agreeValueUnder_clean_monotoneRegime_public
    {predSat : PredSat} {R R' : Regime} {μ₀ μ₁ : Memory}
    {θ₀ θ₁ : RealizationMap} {qt : QTyp} {v₀ v₁ : Value} :
    Regime.monotoneStep R R' →
    qtypCleanUnder R' qt →
    agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ →
    agreeValueUnder predSat R' μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ := by
  intro hmono hclean hagree
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
          (memberVarsRegimeEvidence_monotone hmono hmemberVars₀)
          (memberCvcrEvidence_monotone hmono hmemberCvcr₀)
          (memberVarsRegimeEvidence_monotone hmono hmemberVars₁)
          (memberCvcrEvidence_monotone hmono hmemberCvcr₁)
          hv₀ hv₁)
      (dirty_internal_arrow := by
        intro qt v₀ v₁ hdirty_internal hisArrow htyp1 htyp2 _hclean
        exact agreeValueUnder.dirty_internal_arrow hdirty_internal hisArrow htyp1 htyp2)
      (clean_internal_parrow := by
        intro st1 st2 p tcls qt tcl x body pbody σcap ρcap₀ ρcap₁ v₀ v₁ hclean_internal hetyp htcl hmatch hcap
          hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁ hv₀ hv₁ ihcap _hclean
        exact agreeValueUnder.clean_internal_parrow hclean_internal hetyp htcl hmatch ihcap
          (memberVarsRegimeEvidence_monotone hmono hmemberVars₀)
          (memberCvcrEvidence_monotone hmono hmemberCvcr₀)
          (memberVarsRegimeEvidence_monotone hmono hmemberVars₁)
          (memberCvcrEvidence_monotone hmono hmemberCvcr₁)
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
          exact hdirty (qtypCleanUnder_of_monotone hmono hcleanR')
        exact agreeCapturedEnv.cons_dirty hdirty' hlookup1 hlookup2 htyp1 htyp2 ihtail)
      hagree
  exact hrec hclean

private lemma agreeValueUnder_transport_insert_clean_monotone
    {predSat : PredSat} {R R' : Regime}
    {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
    {qt : QTyp} {v₀ v₁ : Value}
    (a₀ a₁ : Address) (n₀ n₁ : Int)
    (hpred_compat₀ : ∀ (qt : QTyp) (v : Value),
      qtypPredHolds predSat qt μ₀ v ↔
        qtypPredHolds predSat qt (Std.ExtTreeMap.insert μ₀ a₀ n₀) v)
    (hpred_compat₁ : ∀ (qt : QTyp) (v : Value),
      qtypPredHolds predSat qt μ₁ v ↔
        qtypPredHolds predSat qt (Std.ExtTreeMap.insert μ₁ a₁ n₁) v) :
    Regime.monotoneStep R R' →
    qtypCleanUnder R' qt →
    agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ →
    agreeValueUnder predSat R'
      (Std.ExtTreeMap.insert μ₀ a₀ n₀)
      (Std.ExtTreeMap.insert μ₁ a₁ n₁)
      θ₀ θ₁ qt v₀ v₁ := by
  intro hmono hclean hagree
  have hagree_mem :
      agreeValueUnder predSat R
        (Std.ExtTreeMap.insert μ₀ a₀ n₀)
        (Std.ExtTreeMap.insert μ₁ a₁ n₁)
        θ₀ θ₁ qt v₀ v₁ :=
    agreeValueUnder_transport_memory hpred_compat₀ hpred_compat₁
      (qtypCleanUnder_of_monotone hmono hclean) hagree
  exact agreeValueUnder_clean_monotoneRegime_public hmono hclean hagree_mem

private lemma agreeOnClean_transport_assign_final_of_split
    (predSat : PredSat)
    (ctxFinal : TypeContext)
    (cf₀ cf₁ : Config) (θ₀2 θ₁2 : RealizationMap)
    (hloc_final :
      ∀ l qt,
        ctxFinal.memEnv.lookup l = some qt →
        qtypCleanUnder ctxFinal.regime qt →
        agreeLocUnder predSat ctxFinal.regime
          cf₀.memory cf₁.memory θ₀2 θ₁2 (l, qt))
    (hvar_final :
      ∀ x qt,
        ctxFinal.varEnv.lookup x = some qt →
        qtypCleanUnder ctxFinal.regime qt →
        agreeVarUnder predSat ctxFinal.regime
          cf₀.memory cf₀.varEnv cf₁.memory cf₁.varEnv θ₀2 θ₁2 (x, qt)) :
    agreeOnClean predSat ctxFinal.regime ctxFinal
      cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁2 := by
  exact ⟨hloc_final, hvar_final⟩

private lemma resultAgreesIfClean_ref_shared_witness
    {predSat : PredSat} {R : Regime}
    {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
    {qt : QTyp} {ls : LocSet} {a₀w a₁w : Address}
    (hRef : qt.etyp = ETyp.ref ls)
    (hres_agree1 : resultAgreesIfClean predSat R μ₀ μ₁ θ₀ θ₁ qt (Value.loc a₀w) (Value.loc a₁w))
    (hclean : qtypCleanUnder R qt) :
    ∃ lw, lw ∈ ls ∧ θ₀.lookup lw = some a₀w ∧ θ₁.lookup lw = some a₁w := by
  have hagree : agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt (Value.loc a₀w) (Value.loc a₁w) :=
    hres_agree1 hclean
  cases hagree with
  | clean_eq_nonref_nonarrow _ _ hnotref _ =>
      exfalso
      exact hnotref ⟨ls, hRef⟩
  | clean_internal_arrow _ hetyp _ _ _ _ _ =>
      exfalso
      rw [hRef] at hetyp
      cases hetyp
  | dirty_internal_arrow _ hisArrow _ _ =>
      exfalso
      simp [hRef, ETyp.isArrow] at hisArrow
  | clean_internal_parrow _ hetyp _ _ _ _ _ =>
      exfalso
      rw [hRef] at hetyp
      cases hetyp
  | dirty_internal_parrow _ hisParrow _ _ =>
      exfalso
      simp [hRef, ETyp.isParrow] at hisParrow
  | clean_ref _ hetyp hlookup1 hin hv1 hlookup2 hv2 =>
      rw [hRef] at hetyp
      cases hetyp
      cases hv1
      cases hv2
      exact ⟨_, hin, hlookup1, hlookup2⟩
  | withPred_true_eq _ _ _ _ hnotref _ =>
      exfalso
      exact hnotref ⟨ls, hRef⟩
  | withPred_true_ref _ _ _ hetyp hlookup1 hin hv1 hlookup2 hv2 =>
      rw [hRef] at hetyp
      cases hetyp
      cases hv1
      cases hv2
      exact ⟨_, hin, hlookup1, hlookup2⟩

private lemma agreeValueUnder_num_num_eq
    {predSat : PredSat} {R : Regime} {μ₀ μ₁ : Memory}
    {θ₀ θ₁ : RealizationMap} {qt : QTyp} {n₀ n₁ : Int}
    (hagree :
      agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt (Value.num n₀) (Value.num n₁)) :
    n₀ = n₁ := by
  cases hagree with
  | clean_eq_nonref_nonarrow _ _ _ hEq =>
      cases hEq
      rfl
  | withPred_true_eq _ _ _ _ _ hEq =>
      cases hEq
      rfl
  | clean_internal_arrow _ _ _ _ _ _ _ _ _ hv₀ _ =>
      cases hv₀
  | dirty_internal_arrow _ hisArrow htyp₀ _ =>
      have hnum : qt.etyp = ETyp.int := valueHasETyp_num_etyp htyp₀
      simp [hnum, ETyp.isArrow] at hisArrow
  | clean_internal_parrow _ _ _ _ _ _ _ _ _ hv₀ _ =>
      cases hv₀
  | dirty_internal_parrow _ hisParrow htyp₀ _ =>
      have hnum : qt.etyp = ETyp.int := valueHasETyp_num_etyp htyp₀
      simp [hnum, ETyp.isParrow] at hisParrow
  | clean_ref _ _ _ _ hv₀ _ _ =>
      cases hv₀
  | withPred_true_ref _ _ _ _ _ _ hv₀ _ _ =>
      cases hv₀

private lemma tagEnvConsistentWithRegime_invalidateRegimeDeps
    (tagEnv : TagEnv) (R : Regime) (ls : LocSet)
    (h : tagEnvConsistentWithRegime tagEnv R) :
    tagEnvConsistentWithRegime (invalidateTagDeps tagEnv ls) (invalidateRegimeDeps R tagEnv ls) := by
  intro k deps hget
  have hkR : R.lookup? k = some true := by
    have hkeep : tagEnv.get? k = some ⟨true, deps⟩ := by
      unfold invalidateTagDeps at hget
      rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_filter'] at hget
      cases h0 : tagEnv.get? k with
      | none =>
          rw [← Std.ExtTreeMap.get?_eq_getElem?, h0] at hget
          simp at hget
      | some tv =>
          rw [← Std.ExtTreeMap.get?_eq_getElem?, h0] at hget
          simp at hget
          rw [hget.1]
    exact h k deps hkeep
  have hcontains : (invalidateTagDeps tagEnv ls).contains k = true := by
    simp only [Std.ExtTreeMap.contains_eq_isSome_getElem?]
    rw [← Std.ExtTreeMap.get?_eq_getElem?, hget]
    rfl
  exact invalidateRegimeDeps_preserves_lookup_of_surviving_tag R tagEnv ls k true hkR hcontains

private lemma tagEnvConsistentWithRegimeMasked_invalidateRegimeDeps
    (masked : Tag → Prop)
    (tagEnv : TagEnv) (R : Regime) (ls : LocSet)
    (h : tagEnvConsistentWithRegimeMasked masked tagEnv R) :
    tagEnvConsistentWithRegimeMasked masked (invalidateTagDeps tagEnv ls) (invalidateRegimeDeps R tagEnv ls) := by
  intro k deps hget
  have hkR : masked k ∨ R.lookup? k = some true := by
    have hkeep : tagEnv.get? k = some ⟨true, deps⟩ := by
      unfold invalidateTagDeps at hget
      rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_filter'] at hget
      cases h0 : tagEnv.get? k with
      | none =>
          rw [← Std.ExtTreeMap.get?_eq_getElem?, h0] at hget
          simp at hget
      | some tv =>
          rw [← Std.ExtTreeMap.get?_eq_getElem?, h0] at hget
          simp at hget
          rw [hget.1]
    exact h k deps hkeep
  cases hkR with
  | inl hmasked =>
      exact Or.inl hmasked
  | inr hkR =>
      have hcontains : (invalidateTagDeps tagEnv ls).contains k = true := by
        simp only [Std.ExtTreeMap.contains_eq_isSome_getElem?]
        rw [← Std.ExtTreeMap.get?_eq_getElem?, hget]
        rfl
      exact Or.inr <|
        invalidateRegimeDeps_preserves_lookup_of_surviving_tag
          R tagEnv ls k true hkR hcontains

-- updateLocsetWeak_contains_eq_or_mem: moved to TypeSafety.lean
-- assign_memEnv_formula_contains_eq_or_mem: moved to TypeSafety.lean

/--
If every `tagEnv` entry at tag `k` depends on locations from `ls`, then
`invalidateRegimeDeps` drops `k` from the regime.
-/
private lemma assign_updated_new_guardClosure_implies_invalidated_regime_none
    (R : Regime) (tagEnv : TagEnv) (ls : LocSet) (k : Tag)
    (htagInvalid : ∀ tv, tagEnv.get? k = some tv → tv.deps.any ls.contains = true) :
    (invalidateRegimeDeps R tagEnv ls).lookup? k = none := by
  have hkeep_lookup : (invalidateTagDeps tagEnv ls).get? k = none := by
    unfold invalidateTagDeps
    rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_filter']
    rw [← Std.ExtTreeMap.get?_eq_getElem?]
    cases hget : tagEnv.get? k with
    | none =>
        simp
    | some tv =>
        have hdeps : tv.deps.any ls.contains = true := htagInvalid tv hget
        simp [hdeps]
  have hkeep_false : (invalidateTagDeps tagEnv ls).contains k = false := by
    have hkeep_lookup' : (invalidateTagDeps tagEnv ls)[k]? = none := by
      simpa [Std.ExtTreeMap.get?_eq_getElem?] using hkeep_lookup
    have hcontains :
        (invalidateTagDeps tagEnv ls).contains k = ((invalidateTagDeps tagEnv ls)[k]?).isSome :=
      Std.ExtTreeMap.contains_eq_isSome_getElem?
    rw [hcontains, hkeep_lookup']
    decide
  by_contra hnone
  have hsurvive : (invalidateTagDeps tagEnv ls).contains k = true :=
    invalidateRegimeDeps_survives_of_lookup_ne_none R tagEnv ls k hnone
  have : False := by
    simp [hkeep_false] at hsurvive
  exact this.elim

private lemma typecheckIf_ok_pred_noPred
    (ctx : TypeContext) (e1 e2 e3 : Expr) (fuel : Nat) (res : TypeResult)
    (htc : typecheckIf ctx e1 e2 e3 fuel = .ok res) :
    res.qualType.pred = Predicate.noPred := by
  exact typecheckIf_pred_noPred ctx e1 e2 e3 fuel res htc

private lemma typecheckVar_guardClosure_pred_implies_tag_absent
    (ctx : TypeContext) (x : Name) (res : TypeResult)
    (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
    (htc : typecheckVar ctx x = .ok res)
    (hpred : res.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env) :
    res.tagEnv'.get? k = none := by
  unfold typecheckVar at htc
  cases hlookup : ctx.varEnv.lookup x with
  | none =>
      simp [hlookup] at htc
  | some qt =>
      rcases hqt : qt with ⟨etyp, poison, pred⟩
      cases pred with
      | noPred =>
          exfalso
          have hpredNo : res.qualType.pred = Predicate.noPred := by
            have htc' := htc
            simp [hlookup, hqt, pure, Except.pure] at htc'
            cases htc'
            rfl
          simp [hpredNo] at hpred
      | guardOnly kg =>
          exfalso
          cases hfun : etyp.isFunctionType with
          | true =>
              simp [hlookup, hqt, hfun, bind, Except.bind] at htc
          | false =>
              cases hkg : ctx.tagEnv.get? kg with
              | some tv =>
                  cases tv with
                  | mk b deps =>
                      have hpredNo : res.qualType.pred = Predicate.noPred := by
                        have htc' := htc
                        have hkg' : ctx.tagEnv[kg]? = some ⟨b, deps⟩ := by
                          simpa [Std.ExtTreeMap.get?_eq_getElem?] using hkg
                        cases b with
                        | true =>
                            have hkgT : ctx.tagEnv[kg]? = some ⟨true, deps⟩ := by
                              simp [hkg']
                            simp [hlookup, hqt, hfun, hkgT, bind, Except.bind, pure, Except.pure] at htc'
                            cases htc'
                            rfl
                        | false =>
                            have hkgF : ctx.tagEnv[kg]? = some ⟨false, deps⟩ := by
                              simp [hkg']
                            simp [hlookup, hqt, hfun, hkgF, bind, Except.bind, pure, Except.pure] at htc'
                            cases htc'
                            rfl
                      simp [hpredNo] at hpred
              | none =>
                  have hpredGo : res.qualType.pred = Predicate.guardOnly kg := by
                    have htc' := htc
                    have hkg' : ctx.tagEnv[kg]? = none := by
                      simpa [Std.ExtTreeMap.get?_eq_getElem?] using hkg
                    simp [hlookup, hqt, hfun, hkg', bind, Except.bind, pure, Except.pure] at htc'
                    cases htc'
                    rfl
                  simp [hpredGo] at hpred
      | guardClosure kg an pb ve =>
          cases hfun : etyp.isFunctionType with
          | true =>
              exfalso
              simp [hlookup, hqt, hfun, bind, Except.bind] at htc
          | false =>
              cases hkg : ctx.tagEnv.get? kg with
              | some tv =>
                  cases tv with
                  | mk b deps =>
                      exfalso
                      have hpredNo : res.qualType.pred = Predicate.noPred := by
                        have htc' := htc
                        have hkg' : ctx.tagEnv[kg]? = some ⟨b, deps⟩ := by
                          simpa [Std.ExtTreeMap.get?_eq_getElem?] using hkg
                        cases b with
                        | true =>
                            have hkgT : ctx.tagEnv[kg]? = some ⟨true, deps⟩ := by
                              simp [hkg']
                            simp [hlookup, hqt, hfun, hkgT, bind, Except.bind, pure, Except.pure] at htc'
                            cases htc'
                            rfl
                        | false =>
                            have hkgF : ctx.tagEnv[kg]? = some ⟨false, deps⟩ := by
                              simp [hkg']
                            simp [hlookup, hqt, hfun, hkgF, bind, Except.bind, pure, Except.pure] at htc'
                            cases htc'
                            rfl
                      simp [hpredNo] at hpred
              | none =>
                  have hpredRes : res.qualType.pred = Predicate.guardClosure kg an pb ve := by
                    have htc' := htc
                    have hkg' : ctx.tagEnv[kg]? = none := by
                      simpa [Std.ExtTreeMap.get?_eq_getElem?] using hkg
                    simp [hlookup, hqt, hfun, hkg', bind, Except.bind, pure, Except.pure] at htc'
                    cases htc'
                    rfl
                  have hEq :
                      Predicate.guardClosure kg an pb ve =
                        Predicate.guardClosure k arg_name pred_body var_env := by
                    simpa [hpredRes] using hpred
                  have hkEq : kg = k := by
                    cases hEq
                    rfl
                  have htagEq : res.tagEnv' = ctx.tagEnv := by
                    have htc' := htc
                    have hkg' : ctx.tagEnv[kg]? = none := by
                      simpa [Std.ExtTreeMap.get?_eq_getElem?] using hkg
                    simp [hlookup, hqt, hfun, hkg', bind, Except.bind, pure, Except.pure] at htc'
                    cases htc'
                    rfl
                  have hnoneKg : res.tagEnv'.get? kg = none := by
                    simpa [htagEq] using hkg
                  simpa [hkEq] using hnoneKg

private lemma typecheckDeref_guardClosure_pred_implies_tag_absent
    (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
    (htc : typecheckDeref ctx e fuel = .ok res)
    (hpred : res.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env) :
    res.tagEnv'.get? k = none := by
  cases fuel with
  | zero =>
      simp [typecheckDeref] at htc
  | succ fuel' =>
      unfold typecheckDeref at htc
      simp [bind, Except.bind] at htc
      cases htc1 : typecheckExpr ctx e fuel' with
      | error err =>
          simp [htc1] at htc
      | ok result1 =>
          simp [htc1] at htc
          cases hq1 : result1.qualType with
          | mk etyp1 p1 pred1 =>
              simp [hq1] at htc
              cases etyp1 with
              | ref ls =>
                  by_cases hls : ls = ∅
                  · simp [hls] at htc
                  · simp [hls] at htc
                    cases hfold :
                      (ls.foldM (m := Except String) (false, (none : Option Predicate))
                        (fun x l =>
                          match result1.memEnv'.lookup l with
                          | some qt =>
                              pure
                                (joinPoison x.1 qt.poison,
                                  match x.2 with
                                  | none => some qt.pred
                                  | some p => some (joinPredicates p qt.pred))
                          | none =>
                              throw
                                (toString "Location " ++ toString l ++ toString " not found in memory environment"))) with
                  | error err =>
                      erw [hfold] at htc
                      simp at htc
                      cases htc
                  | ok v =>
                      erw [hfold] at htc
                      cases hp1 : p1 with
                      | true =>
                          simp [hp1, pure, Except.pure] at htc
                          cases htc
                          simp at hpred
                      | false =>
                          simp [hp1] at htc
                          cases hmerged : v.2.getD Predicate.noPred with
                          | noPred =>
                              simp [hmerged, pure, Except.pure] at htc
                              cases htc
                              simp at hpred
                          | guardOnly kg =>
                              cases hkg : result1.tagEnv'[kg]? with
                              | some tv =>
                                  cases tv with
                                  | mk b deps =>
                                      cases b with
                                      | true =>
                                          simp [hmerged, hkg, pure, Except.pure] at htc
                                          cases htc
                                          simp at hpred
                                      | false =>
                                          simp [hmerged, hkg, pure, Except.pure] at htc
                                          cases htc
                                          simp at hpred
                              | none =>
                                  simp [hmerged, hkg, pure, Except.pure] at htc
                                  cases htc
                                  simp at hpred
                          | guardClosure kg an pb ve =>
                              cases hkg : result1.tagEnv'[kg]? with
                              | some tv =>
                                  cases tv with
                                  | mk b deps =>
                                      cases b with
                                      | true =>
                                          simp [hmerged, hkg, pure, Except.pure] at htc
                                          cases htc
                                          simp at hpred
                                      | false =>
                                          simp [hmerged, hkg, pure, Except.pure] at htc
                                          cases htc
                                          simp at hpred
                              | none =>
                                  simp [hmerged, hkg, pure, Except.pure] at htc
                                  have hEq :
                                      { qualType :=
                                          { etyp := ETyp.int
                                            poison := joinPoison ctx.pc v.1
                                            pred := Predicate.guardClosure kg an pb ve }
                                        memEnv' := result1.memEnv'
                                        tagEnv' := result1.tagEnv'
                                        nextLoc' := result1.nextLoc'
                                        nextTag' := result1.nextTag'
                                        regime' := result1.regime' } = res := by
                                    simpa using htc
                                  have hpredRes : res.qualType.pred = Predicate.guardClosure kg an pb ve := by
                                    have h := congrArg (fun r => r.qualType.pred) hEq.symm
                                    simpa using h
                                  have hkEq : kg = k := by
                                    have : Predicate.guardClosure kg an pb ve =
                                        Predicate.guardClosure k arg_name pred_body var_env := by
                                      simpa [hpredRes] using hpred
                                    cases this
                                    rfl
                                  have htagEq : res.tagEnv' = result1.tagEnv' := by
                                    have h := congrArg TypeResult.tagEnv' hEq.symm
                                    simpa using h
                                  have hnoneKg : res.tagEnv'.get? kg = none := by
                                    simpa [htagEq] using hkg
                                  simpa [hkEq] using hnoneKg
              | _ => simp at htc

private lemma joinTagEnvs_get?_none_of_left_none
    (accTag tagEnv : TagEnv) (k : Tag)
    (hacc : accTag.get? k = none) :
    (joinTagEnvs accTag tagEnv).get? k = none := by
  classical
  unfold joinTagEnvs
  set f : Tag → Option TagVal → Option TagVal → Option TagVal :=
    fun _ otv1 otv2 =>
      match otv1, otv2 with
      | some ⟨b1, deps1⟩, some ⟨b2, deps2⟩ =>
          if b1 == b2 then
            some ⟨b1, LocSet.union deps1 deps2⟩
          else
            none
      | some _, none => none
      | none, some _ => none
      | none, none => none
  set ks : List Tag := (accTag.keys ++ tagEnv.keys).eraseDups
  change (combineExtTreeMaps.go accTag tagEnv f ks ({} : TagEnv)).get? k = none
  rw [Std.ExtTreeMap.get?_eq_getElem?]
  by_cases hmem : k ∈ ks
  · have hgo := combineExtTreeMaps_go_get_mem accTag tagEnv f ks ({} : TagEnv) k hmem
    have hacc_elem : accTag[k]? = none := by
      simpa [Std.ExtTreeMap.get?_eq_getElem?] using hacc
    have hfnone : f k accTag[k]? tagEnv[k]? = none := by
      cases htag : tagEnv[k]? <;> simp [f, hacc_elem]
    simpa [hfnone] using hgo
  · have hgo := combineExtTreeMaps_go_get_not_mem accTag tagEnv f ks ({} : TagEnv) k hmem
    simpa using hgo

private lemma typecheckApp_arrow_branch_guardClosure_pred_implies_tag_absent
    (ctx : TypeContext) (res : TypeResult)
    (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
    (fuel' : Nat)
    (ih :
      ∀ m < fuel' + 1 + 1,
        ∀ (ctx : TypeContext) (e : Expr) (res : TypeResult),
          typecheckExpr ctx e m = Except.ok res →
          TagBoundedCtx ctx →
          res.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env →
          Std.ExtTreeMap.get? res.tagEnv' k = none)
    (st1 st2 : Typ) (p p1 : Poison) (etyp2 : ETyp) (p2 : Poison) (pred2 : Predicate)
    (result1 : TypeResult)
    (hbound_result1 : tagEnvBounded result1.tagEnv' result1.nextTag')
    (hEtyp1 : result1.qualType.etyp = ETyp.arrow st1 st2 p tcls)
    (hClosFull : ∀ tcl ∈ tcls, match tcl with
        | .regular _ _ env => CapturedEnvFullBounded env result1.nextTag'
        | .extern _ _ _ env => CapturedEnvFullBounded env result1.nextTag')
    (hPredM1 : predTagsBoundedInMemEnv result1.memEnv' result1.nextTag')
    (hArgPred : qtypPredTagBounded ⟨etyp2, joinPoison ctx.pc p2, pred2⟩ result1.nextTag')
    (hArgClos : etypClosuresFullBounded (⟨etyp2, joinPoison ctx.pc p2, pred2⟩ : QTyp).etyp result1.nextTag')
    (results : List TypeResult) (first : TypeResult) (rest : List TypeResult)
    (hmap :
      List.mapM
        (fun tcl =>
          applyFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel')
        tcls = Except.ok results)
    (hresults : results = first :: rest)
    (hjoin : joinTypeResults ctx first rest = Except.ok res)
    (hpred : res.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env) :
    Std.ExtTreeMap.get? res.tagEnv' k = none := by
  have hjoin' := hjoin
  unfold joinTypeResults at hjoin'
  simp [bind, Except.bind] at hjoin'
  cases hqf : first.qualType with
  | mk firstEtyp firstPoison firstPred =>
      simp [hqf] at hjoin'
      cases hcheck :
          List.foldlM
            (fun x result =>
              match result.qualType with
              | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                if beqETypSignature firstEtyp resEtyp = false then
                  Except.error
                    (toString "Closure alternatives produced incompatible result types: " ++ toString (repr firstEtyp) ++
                        toString " vs " ++
                      toString (repr resEtyp))
                else
                  Except.ok ())
            () rest with
      | error err =>
          erw [hcheck] at hjoin'
          cases hjoin'
      | ok _ =>
          erw [hcheck] at hjoin'
          cases hfold :
              (List.foldlM
                (fun acc result =>
                  match result.qualType with
                  | { etyp := resEtyp, poison := resPoison, pred := resPred } =>
                    pure
                      (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                        joinMemEnvsStrong acc.2.1 result.memEnv',
                        joinPoison acc.2.2.1 resPoison,
                        joinPredicates acc.2.2.2.1 resPred,
                        joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
                        joinRegimes acc.2.2.2.2.2.1 result.regime',
                        max acc.2.2.2.2.2.2.1 result.nextLoc',
                        max acc.2.2.2.2.2.2.2 result.nextTag'))
                (firstEtyp, first.memEnv', firstPoison, firstPred, first.tagEnv', first.regime',
                  first.nextLoc', first.nextTag')
                rest : Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)) with
          | error err =>
              erw [hfold] at hjoin'
              simp at hjoin'
          | ok joined =>
              erw [hfold] at hjoin'
              simp [pure, Except.pure] at hjoin'
              have hjoin_ok :
                  { qualType :=
                      { etyp := joined.1
                        poison := joinPoison ctx.pc joined.2.2.1
                        pred :=
                          match joined.1 with
                          | ETyp.arrow _ _ _ _ => Predicate.noPred
                          | ETyp.parrow _ _ _ _ => Predicate.noPred
                          | _ => joined.2.2.2.1 }
                    memEnv' := joined.2.1
                    tagEnv' := joined.2.2.2.2.1
                    nextLoc' := joined.2.2.2.2.2.2.1
                    nextTag' := joined.2.2.2.2.2.2.2
                    regime' := joined.2.2.2.2.2.1 } = res := by
                cases hjoin'
                rfl
              have hresPred :
                  (match joined.1 with
                  | ETyp.arrow _ _ _ _ => Predicate.noPred
                  | ETyp.parrow _ _ _ _ => Predicate.noPred
                  | _ => joined.2.2.2.1) = Predicate.guardClosure k arg_name pred_body var_env := by
                calc
                  (match joined.1 with
                  | ETyp.arrow _ _ _ _ => Predicate.noPred
                  | ETyp.parrow _ _ _ _ => Predicate.noPred
                  | _ => joined.2.2.2.1) = res.qualType.pred := by
                    cases hjoin'
                    rfl
                  _ = Predicate.guardClosure k arg_name pred_body var_env := hpred
              have hjoinedPred : joined.2.2.2.1 = Predicate.guardClosure k arg_name pred_body var_env := by
                cases hE : joined.1 <;> (simp [hE] at hresPred; try exact hresPred)
              have hfirstPred : firstPred = Predicate.guardClosure k arg_name pred_body var_env := by
                have hpred_of_fold :
                    ∀ (rest : List TypeResult)
                      (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
                      (joined : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
                      List.foldlM (m := Except String)
                        (fun acc result =>
                          match result.qualType with
                          | { etyp := resEtyp, poison := resPoison, pred := resPred } =>
                            Except.ok
                              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                                joinMemEnvsStrong acc.2.1 result.memEnv',
                                joinPoison acc.2.2.1 resPoison,
                                joinPredicates acc.2.2.2.1 resPred,
                                joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
                                joinRegimes acc.2.2.2.2.2.1 result.regime',
                                max acc.2.2.2.2.2.2.1 result.nextLoc',
                                max acc.2.2.2.2.2.2.2 result.nextTag'))
                        acc rest = Except.ok joined →
                      joined.2.2.2.1 = Predicate.guardClosure k arg_name pred_body var_env →
                      acc.2.2.2.1 = Predicate.guardClosure k arg_name pred_body var_env := by
                  intro rest
                  induction rest with
                  | nil =>
                      intro acc joined hfold hjoinedPred
                      simp [List.foldlM_nil] at hfold
                      cases hfold
                      simpa using hjoinedPred
                  | cons r rs ihr =>
                      intro acc joined hfold hjoinedPred
                      cases hq : r.qualType with
                      | mk resEtyp resPoison resPred =>
                          simp [List.foldlM_cons, hq, bind, Except.bind] at hfold
                          have haccPred :
                              joinPredicates acc.2.2.2.1 resPred =
                                Predicate.guardClosure k arg_name pred_body var_env := by
                            exact ihr _ _ hfold hjoinedPred
                          exact
                            (joinPredicates_eq_guardClosure
                              (p := acc.2.2.2.1) (q := resPred)
                              (k := k) (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
                              haccPred).1
                simpa using
                  hpred_of_fold
                    rest
                    (firstEtyp, first.memEnv', firstPoison, firstPred, first.tagEnv', first.regime',
                      first.nextLoc', first.nextTag')
                    joined
                    hfold
                    hjoinedPred
              have hfirstPredQ : first.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env := by
                simpa [hqf] using hfirstPred
              have hhead :
                  ∃ tcl0 tcls', tcls = tcl0 :: tcls' ∧
                    applyFnTClosure tcl0 st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel' = .ok first := by
                have hForall2 :
                    List.Forall₂
                      (fun tcl r => applyFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel' = .ok r)
                      tcls results :=
                  List.mapM_Except_ok_implies_forall2 tcls
                    (fun tcl => applyFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel')
                    results hmap
                rw [hresults] at hForall2
                cases hForall2 with
                | @cons tcl0 first0 tcls' rest' hhead htail =>
                    exact ⟨tcl0, tcls', rfl, by simpa using hhead⟩
              rcases hhead with ⟨tcl0, tcls', htcls, happly⟩
              have hfirstTagNone : first.tagEnv'.get? k = none := by
                cases tcl0 with
                | regular x body env =>
                    unfold applyFnTClosure at happly
                    cases fuel' with
                    | zero =>
                        simp at happly
                    | succ fuel'' =>
                        simp [bind, Except.bind] at happly
                        cases htcBody :
                            typecheckExpr
                              { ctx with
                                pc := joinPoison p (joinPoison p1 ctx.pc)
                                memEnv := result1.memEnv'
                                varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                                  { etyp := etyp2, poison := joinPoison ctx.pc p2, pred := pred2 }
                                tagEnv := result1.tagEnv'
                                nextTag := result1.nextTag'
                                nextLoc := result1.nextLoc'
                                regime := result1.regime' }
                              body fuel'' with
                        | error err =>
                            simp [htcBody] at happly
                        | ok result3 =>
                            simp [htcBody] at happly
                            cases hq3 : result3.qualType with
                            | mk etyp3 p3 pred3 =>
                                simp [hq3] at happly
                                cases hsub : isSubtype st2 { etyp := etyp3, poison := p3, pred := pred3 } with
                                | false =>
                                    simp [hsub] at happly
                                | true =>
                                    simp [hsub, pure, Except.pure] at happly
                                    have hfirstEq :
                                        first =
                                          { qualType :=
                                              normalizeAppResultByProvenance (joinPoison p1 p)
                                                { etyp := etyp3
                                                  poison := joinPoison p1 (joinPoison p p3)
                                                  pred := pred3 }
                                            memEnv' := result3.memEnv'
                                            tagEnv' := result3.tagEnv'
                                            nextLoc' := result3.nextLoc'
                                            nextTag' := result3.nextTag'
                                            regime' := result3.regime' } := by
                                      simpa using happly.symm
                                    by_cases hp1pT : (joinPoison p1 p) = true
                                    ·
                                        have : first.qualType.pred = Predicate.noPred := by
                                          simp [hfirstEq, normalizeAppResultByProvenance, hp1pT]
                                        have : False := by
                                          simp [this] at hfirstPredQ
                                        exact False.elim this
                                    ·
                                        have hpred3 : pred3 = Predicate.guardClosure k arg_name pred_body var_env := by
                                          have hpredEq : first.qualType.pred = pred3 := by
                                            simp [hfirstEq, normalizeAppResultByProvenance, hp1pT]
                                          simp [hpredEq] at hfirstPredQ
                                          exact hfirstPredQ
                                        have hltFuel : fuel'' < fuel'' + 1 + 1 + 1 := by
                                          simp [Nat.add_assoc]
                                        have hbodyBounded : TagBoundedCtx
                                            { ctx with
                                              pc := joinPoison p (joinPoison p1 ctx.pc)
                                              memEnv := result1.memEnv'
                                              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                                                { etyp := etyp2, poison := joinPoison ctx.pc p2, pred := pred2 }
                                              tagEnv := result1.tagEnv'
                                              nextTag := result1.nextTag'
                                              nextLoc := result1.nextLoc'
                                              regime := result1.regime' } := by
                                          have hCapBound : CapturedEnvFullBounded env result1.nextTag' :=
                                            hClosFull _ (by rw [htcls]; exact .head _)
                                          exact ⟨hbound_result1,
                                            ⟨predTagsBoundedInVarEnv_update
                                              (predTagsBoundedInVarEnv_ofCaptured (capturedPredTagsBounded_of_fullBounded hCapBound))
                                              hArgPred,
                                             hPredM1⟩,
                                            varEnvClosuresCapturedBounded_update
                                              (varEnvClosuresCapturedBounded_ofCaptured hCapBound)
                                              hArgClos⟩
                                        have hnone3 : result3.tagEnv'.get? k = none :=
                                          ih fuel'' hltFuel
                                            { ctx with
                                              pc := joinPoison p (joinPoison p1 ctx.pc)
                                              memEnv := result1.memEnv'
                                              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                                                { etyp := etyp2, poison := joinPoison ctx.pc p2, pred := pred2 }
                                              tagEnv := result1.tagEnv'
                                              nextTag := result1.nextTag'
                                              nextLoc := result1.nextLoc'
                                              regime := result1.regime' }
                                            body result3 htcBody hbodyBounded (by simpa [hq3] using hpred3)
                                        simpa [hfirstEq] using hnone3
                | extern x retSpec effects capturedEnv =>
                    exact applyFnTClosure_extern_ok_guardClosure_tag_absent_of_tagEnvBounded ctx st1 st2 p p1
                      etyp2 p2 pred2 result1 fuel' x retSpec effects capturedEnv first
                      hbound_result1 happly
                      k arg_name pred_body var_env hfirstPredQ
              have hjoinedTagNone : joined.2.2.2.2.1.get? k = none := by
                have htag_none_of_fold :
                    ∀ (rest : List TypeResult)
                      (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
                      (joined : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
                      List.foldlM (m := Except String)
                        (fun acc result =>
                          match result.qualType with
                          | { etyp := resEtyp, poison := resPoison, pred := resPred } =>
                            Except.ok
                              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                                joinMemEnvsStrong acc.2.1 result.memEnv',
                                joinPoison acc.2.2.1 resPoison,
                                joinPredicates acc.2.2.2.1 resPred,
                                joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
                                joinRegimes acc.2.2.2.2.2.1 result.regime',
                                max acc.2.2.2.2.2.2.1 result.nextLoc',
                                max acc.2.2.2.2.2.2.2 result.nextTag'))
                        acc rest = Except.ok joined →
                      acc.2.2.2.2.1.get? k = none →
                      joined.2.2.2.2.1.get? k = none := by
                  intro rest
                  induction rest with
                  | nil =>
                      intro acc joined hfold haccNone
                      simp [List.foldlM_nil, pure, Except.pure] at hfold
                      cases hfold
                      simpa using haccNone
                  | cons r rs ihr =>
                      intro acc joined hfold haccNone
                      cases hq : r.qualType with
                      | mk resEtyp resPoison resPred =>
                          simp [List.foldlM_cons, hq, bind, Except.bind] at hfold
                          have haccNone' : (joinTagEnvs acc.2.2.2.2.1 r.tagEnv').get? k = none := by
                            exact joinTagEnvs_get?_none_of_left_none acc.2.2.2.2.1 r.tagEnv' k haccNone
                          exact ihr _ _ hfold haccNone'
                simpa [hqf] using
                  htag_none_of_fold
                    rest
                    (firstEtyp, first.memEnv', firstPoison, firstPred, first.tagEnv', first.regime',
                      first.nextLoc', first.nextTag')
                    joined
                    hfold
                    hfirstTagNone
              have hresTag : res.tagEnv' = joined.2.2.2.2.1 := by
                have htagEq :
                    joined.2.2.2.2.1 = res.tagEnv' := by
                  simpa using congrArg TypeResult.tagEnv' hjoin_ok
                simpa using htagEq.symm
              simpa [hresTag] using hjoinedTagNone

private lemma typecheckApp_parrow_branch_guardClosure_pred_implies_tag_absent
    (ctx : TypeContext) (res : TypeResult)
    (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
    (fuel' : Nat)
    (ih :
      ∀ m < fuel' + 1 + 1,
        ∀ (ctx : TypeContext) (e : Expr) (res : TypeResult),
          typecheckExpr ctx e m = Except.ok res →
          TagBoundedCtx ctx →
          res.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env →
          Std.ExtTreeMap.get? res.tagEnv' k = none)
    (st1 st2 : Typ) (p p1 : Poison) (etyp2 : ETyp) (p2 : Poison) (pred2 : Predicate)
    (result1 : TypeResult)
    (hbound_result1 : tagEnvBounded result1.tagEnv' result1.nextTag')
    (hEtyp1 : result1.qualType.etyp = ETyp.parrow st1 st2 p tcls)
    (hClosFull : ∀ tcl ∈ tcls, match tcl with
        | .regular _ _ env => CapturedEnvFullBounded env result1.nextTag'
        | .extern _ _ env => CapturedEnvFullBounded env result1.nextTag')
    (hPredM1 : predTagsBoundedInMemEnv result1.memEnv' result1.nextTag')
    (hArgPred : qtypPredTagBounded ⟨etyp2, joinPoison ctx.pc p2, pred2⟩ result1.nextTag')
    (hArgClos : etypClosuresFullBounded (⟨etyp2, joinPoison ctx.pc p2, pred2⟩ : QTyp).etyp result1.nextTag')
    (results : List TypeResult) (first : TypeResult) (rest : List TypeResult)
    (hmap :
      List.mapM
        (fun tcl =>
          applyPFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel')
        tcls = Except.ok results)
    (hresults : results = first :: rest)
    (hjoin : joinTypeResults ctx first rest = Except.ok res)
    (hpred : res.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env) :
    Std.ExtTreeMap.get? res.tagEnv' k = none := by
  have hjoin' := hjoin
  unfold joinTypeResults at hjoin'
  simp [bind, Except.bind] at hjoin'
  cases hqf : first.qualType with
  | mk firstEtyp firstPoison firstPred =>
      simp [hqf] at hjoin'
      cases hcheck :
          List.foldlM
            (fun x result =>
              match result.qualType with
              | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                if beqETypSignature firstEtyp resEtyp = false then
                  Except.error
                    (toString "Closure alternatives produced incompatible result types: " ++ toString (repr firstEtyp) ++
                        toString " vs " ++
                      toString (repr resEtyp))
                else
                  Except.ok ())
            () rest with
      | error err =>
          erw [hcheck] at hjoin'
          cases hjoin'
      | ok _ =>
          erw [hcheck] at hjoin'
          cases hfold :
              (List.foldlM
                (fun acc result =>
                  match result.qualType with
                  | { etyp := resEtyp, poison := resPoison, pred := resPred } =>
                    pure
                      (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                        joinMemEnvsStrong acc.2.1 result.memEnv',
                        joinPoison acc.2.2.1 resPoison,
                        joinPredicates acc.2.2.2.1 resPred,
                        joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
                        joinRegimes acc.2.2.2.2.2.1 result.regime',
                        max acc.2.2.2.2.2.2.1 result.nextLoc',
                        max acc.2.2.2.2.2.2.2 result.nextTag'))
                (firstEtyp, first.memEnv', firstPoison, firstPred, first.tagEnv', first.regime',
                  first.nextLoc', first.nextTag')
                rest : Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)) with
          | error err =>
              erw [hfold] at hjoin'
              simp at hjoin'
          | ok joined =>
              erw [hfold] at hjoin'
              simp [pure, Except.pure] at hjoin'
              have hjoin_ok :
                  { qualType :=
                      { etyp := joined.1
                        poison := joinPoison ctx.pc joined.2.2.1
                        pred :=
                          match joined.1 with
                          | ETyp.arrow _ _ _ _ => Predicate.noPred
                          | ETyp.parrow _ _ _ _ => Predicate.noPred
                          | _ => joined.2.2.2.1 }
                    memEnv' := joined.2.1
                    tagEnv' := joined.2.2.2.2.1
                    nextLoc' := joined.2.2.2.2.2.2.1
                    nextTag' := joined.2.2.2.2.2.2.2
                    regime' := joined.2.2.2.2.2.1 } = res := by
                cases hjoin'
                rfl
              have hresPred :
                  (match joined.1 with
                  | ETyp.arrow _ _ _ _ => Predicate.noPred
                  | ETyp.parrow _ _ _ _ => Predicate.noPred
                  | _ => joined.2.2.2.1) = Predicate.guardClosure k arg_name pred_body var_env := by
                calc
                  (match joined.1 with
                  | ETyp.arrow _ _ _ _ => Predicate.noPred
                  | ETyp.parrow _ _ _ _ => Predicate.noPred
                  | _ => joined.2.2.2.1) = res.qualType.pred := by
                    cases hjoin'
                    rfl
                  _ = Predicate.guardClosure k arg_name pred_body var_env := hpred
              have hjoinedPred : joined.2.2.2.1 = Predicate.guardClosure k arg_name pred_body var_env := by
                cases hE : joined.1 <;> (simp [hE] at hresPred; try exact hresPred)
              have hfirstPred : firstPred = Predicate.guardClosure k arg_name pred_body var_env := by
                have hpred_of_fold :
                    ∀ (rest : List TypeResult)
                      (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
                      (joined : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
                      List.foldlM (m := Except String)
                        (fun acc result =>
                          match result.qualType with
                          | { etyp := resEtyp, poison := resPoison, pred := resPred } =>
                            Except.ok
                              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                                joinMemEnvsStrong acc.2.1 result.memEnv',
                                joinPoison acc.2.2.1 resPoison,
                                joinPredicates acc.2.2.2.1 resPred,
                                joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
                                joinRegimes acc.2.2.2.2.2.1 result.regime',
                                max acc.2.2.2.2.2.2.1 result.nextLoc',
                                max acc.2.2.2.2.2.2.2 result.nextTag'))
                        acc rest = Except.ok joined →
                      joined.2.2.2.1 = Predicate.guardClosure k arg_name pred_body var_env →
                      acc.2.2.2.1 = Predicate.guardClosure k arg_name pred_body var_env := by
                  intro rest
                  induction rest with
                  | nil =>
                      intro acc joined hfold hjoinedPred
                      simp [List.foldlM_nil] at hfold
                      cases hfold
                      simpa using hjoinedPred
                  | cons r rs ihr =>
                      intro acc joined hfold hjoinedPred
                      cases hq : r.qualType with
                      | mk resEtyp resPoison resPred =>
                          simp [List.foldlM_cons, hq, bind, Except.bind] at hfold
                          have haccPred :
                              joinPredicates acc.2.2.2.1 resPred =
                                Predicate.guardClosure k arg_name pred_body var_env := by
                            exact ihr _ _ hfold hjoinedPred
                          exact
                            (joinPredicates_eq_guardClosure
                              (p := acc.2.2.2.1) (q := resPred)
                              (k := k) (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
                              haccPred).1
                simpa using
                  hpred_of_fold
                    rest
                    (firstEtyp, first.memEnv', firstPoison, firstPred, first.tagEnv', first.regime',
                      first.nextLoc', first.nextTag')
                    joined
                    hfold
                    hjoinedPred
              have hfirstPredQ : first.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env := by
                simpa [hqf] using hfirstPred
              have hhead :
                  ∃ tcl0 tcls', tcls = tcl0 :: tcls' ∧
                    applyPFnTClosure tcl0 st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel' = .ok first := by
                have hForall2 :
                    List.Forall₂
                      (fun tcl r => applyPFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel' = .ok r)
                      tcls results :=
                  List.mapM_Except_ok_implies_forall2 tcls
                    (fun tcl => applyPFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel')
                    results hmap
                rw [hresults] at hForall2
                cases hForall2 with
                | @cons tcl0 first0 tcls' rest' hhead htail =>
                    exact ⟨tcl0, tcls', rfl, by simpa using hhead⟩
              rcases hhead with ⟨tcl0, tcls', htcls, happly⟩
              have hfirstTagNone : first.tagEnv'.get? k = none := by
                cases tcl0 with
                | regular x pbody env =>
                    unfold applyPFnTClosure at happly
                    cases fuel' with
                    | zero =>
                        simp at happly
                    | succ fuel'' =>
                        simp [bind, Except.bind] at happly
                        cases htcBody :
                            typecheckExpr
                              { ctx with
                                pc := joinPoison p (joinPoison ctx.pc p1)
                                memEnv := result1.memEnv'
                                varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                                  { etyp := etyp2, poison := joinPoison ctx.pc p2, pred := pred2 }
                                tagEnv := result1.tagEnv'
                                pureCtx := true
                                nextTag := result1.nextTag'
                                nextLoc := result1.nextLoc'
                                regime := result1.regime' }
                              (PExpr.toExpr pbody) fuel'' with
                        | error err =>
                            simp [htcBody] at happly
                        | ok result3 =>
                            simp [htcBody] at happly
                            cases hq3 : result3.qualType with
                            | mk etyp3 p3 pred3 =>
                                simp [hq3] at happly
                                cases hsub : isSubtype st2 { etyp := etyp3, poison := p3, pred := pred3 } with
                                | false =>
                                    simp [hsub] at happly
                                | true =>
                                    simp [hsub, pure, Except.pure] at happly
                                    have hfirstEq :
                                        first =
                                          { qualType :=
                                              normalizeAppResultByProvenance (joinPoison p1 p)
                                                { etyp := etyp3
                                                  poison := joinPoison p1 (joinPoison p p3)
                                                  pred := pred3 }
                                            memEnv' := result3.memEnv'
                                            tagEnv' := result3.tagEnv'
                                            nextLoc' := result3.nextLoc'
                                            nextTag' := result3.nextTag'
                                            regime' := result3.regime' } := by
                                      simpa using happly.symm
                                    by_cases hp1pT : (joinPoison p1 p) = true
                                    ·
                                        have : first.qualType.pred = Predicate.noPred := by
                                          simp [hfirstEq, normalizeAppResultByProvenance, hp1pT]
                                        have : False := by
                                          simp [this] at hfirstPredQ
                                        exact False.elim this
                                    ·
                                        have hpred3 : pred3 = Predicate.guardClosure k arg_name pred_body var_env := by
                                          have hpredEq : first.qualType.pred = pred3 := by
                                            simp [hfirstEq, normalizeAppResultByProvenance, hp1pT]
                                          simp [hpredEq] at hfirstPredQ
                                          exact hfirstPredQ
                                        have hltFuel : fuel'' < fuel'' + 1 + 1 + 1 := by
                                          simp [Nat.add_assoc]
                                        have hbodyBounded : TagBoundedCtx
                                            { ctx with
                                              pc := joinPoison p (joinPoison ctx.pc p1)
                                              memEnv := result1.memEnv'
                                              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                                                { etyp := etyp2, poison := joinPoison ctx.pc p2, pred := pred2 }
                                              tagEnv := result1.tagEnv'
                                              pureCtx := true
                                              nextTag := result1.nextTag'
                                              nextLoc := result1.nextLoc'
                                              regime := result1.regime' } := by
                                          have hCapBound : CapturedEnvFullBounded env result1.nextTag' :=
                                            hClosFull _ (by rw [htcls]; exact .head _)
                                          exact ⟨hbound_result1,
                                            ⟨predTagsBoundedInVarEnv_update
                                              (predTagsBoundedInVarEnv_ofCaptured (capturedPredTagsBounded_of_fullBounded hCapBound))
                                              hArgPred,
                                             hPredM1⟩,
                                            varEnvClosuresCapturedBounded_update
                                              (varEnvClosuresCapturedBounded_ofCaptured hCapBound)
                                              hArgClos⟩
                                        have hnone3 : result3.tagEnv'.get? k = none :=
                                          ih fuel'' hltFuel
                                            { ctx with
                                              pc := joinPoison p (joinPoison ctx.pc p1)
                                              memEnv := result1.memEnv'
                                              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                                                { etyp := etyp2, poison := joinPoison ctx.pc p2, pred := pred2 }
                                              tagEnv := result1.tagEnv'
                                              pureCtx := true
                                              nextTag := result1.nextTag'
                                              nextLoc := result1.nextLoc'
                                              regime := result1.regime' }
                                            (PExpr.toExpr pbody) result3 htcBody hbodyBounded (by simpa [hq3] using hpred3)
                                        simpa [hfirstEq] using hnone3
                | extern x retSpec capturedEnv =>
                    exact applyPFnTClosure_extern_ok_guardClosure_tag_absent_of_tagEnvBounded ctx st1 st2 p p1
                      etyp2 p2 pred2 result1 fuel' x retSpec capturedEnv first
                      hbound_result1 happly
                      k arg_name pred_body var_env hfirstPredQ
              have hjoinedTagNone : joined.2.2.2.2.1.get? k = none := by
                have htag_none_of_fold :
                    ∀ (rest : List TypeResult)
                      (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
                      (joined : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
                      List.foldlM (m := Except String)
                        (fun acc result =>
                          match result.qualType with
                          | { etyp := resEtyp, poison := resPoison, pred := resPred } =>
                            Except.ok
                              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                                joinMemEnvsStrong acc.2.1 result.memEnv',
                                joinPoison acc.2.2.1 resPoison,
                                joinPredicates acc.2.2.2.1 resPred,
                                joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
                                joinRegimes acc.2.2.2.2.2.1 result.regime',
                                max acc.2.2.2.2.2.2.1 result.nextLoc',
                                max acc.2.2.2.2.2.2.2 result.nextTag'))
                        acc rest = Except.ok joined →
                      acc.2.2.2.2.1.get? k = none →
                      joined.2.2.2.2.1.get? k = none := by
                  intro rest
                  induction rest with
                  | nil =>
                      intro acc joined hfold haccNone
                      simp [List.foldlM_nil, pure, Except.pure] at hfold
                      cases hfold
                      simpa using haccNone
                  | cons r rs ihr =>
                      intro acc joined hfold haccNone
                      cases hq : r.qualType with
                      | mk resEtyp resPoison resPred =>
                          simp [List.foldlM_cons, hq, bind, Except.bind] at hfold
                          have haccNone' : (joinTagEnvs acc.2.2.2.2.1 r.tagEnv').get? k = none := by
                            exact joinTagEnvs_get?_none_of_left_none acc.2.2.2.2.1 r.tagEnv' k haccNone
                          exact ihr _ _ hfold haccNone'
                simpa [hqf] using
                  htag_none_of_fold
                    rest
                    (firstEtyp, first.memEnv', firstPoison, firstPred, first.tagEnv', first.regime',
                      first.nextLoc', first.nextTag')
                    joined
                    hfold
                    hfirstTagNone
              have hresTag : res.tagEnv' = joined.2.2.2.2.1 := by
                have htagEq :
                    joined.2.2.2.2.1 = res.tagEnv' := by
                  simpa using congrArg TypeResult.tagEnv' hjoin_ok
                simpa using htagEq.symm
              simpa [hresTag] using hjoinedTagNone

private lemma guardClosure_pred_implies_tag_absent
    (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
    (htc : typecheckExpr ctx e fuel = .ok res)
    (hbounded : TagBoundedCtx ctx)
    (hpred : res.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env) :
    res.tagEnv'.get? k = none := by
  revert ctx e res htc hbounded hpred
  refine Nat.strongRecOn fuel ?_
  intro fuel ih ctx e res htc hbounded hpred
  cases fuel with
  | zero =>
      simp [typecheckExpr] at htc
  | succ fuel =>
      cases e with
      | unit =>
          exfalso
          simp [typecheckExpr, typecheckUnit] at htc
          cases htc
          simp at hpred
      | num _ =>
          exfalso
          simp [typecheckExpr, typecheckInt] at htc
          cases htc
          simp at hpred
      | bool _ =>
          exfalso
          simp [typecheckExpr, typecheckBool] at htc
          cases htc
          simp at hpred
      | str _ =>
          exfalso
          simp [typecheckExpr, typecheckString] at htc
          cases htc
          simp at hpred
      | fn _ _ _ _ =>
          exfalso
          simp [typecheckExpr, typecheckFn] at htc
          cases htc
          simp at hpred
      | pfn x t1 body t2 =>
          exfalso
          simp [typecheckExpr, typecheckPfn] at htc
          cases htcBody : Expr.toPExpr body with
          | error _ =>
              simp [htcBody] at htc
          | ok _ =>
              simp [htcBody] at htc
              cases htc
              simp at hpred
      | unaryop op e1 =>
          have htc' : typecheckUnaryOp ctx op e1 fuel = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckUnaryOp_structure ctx op e1 fuel res htc' with
            ⟨result1, result_etyp, htc1, hop, hmem, htag, hnextLoc, hnextTag, hreg, hetyp, hpoison, hpredNo⟩
          exfalso
          simp [hpredNo] at hpred
      | op e1 op e2 =>
          have htc' : typecheckOp ctx e1 e2 fuel op = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckOp_structure ctx e1 e2 op fuel res htc' with
            ⟨result1, result2, result_etyp, htc1, htc2, hop, hmem, htag, hnextLoc, hnextTag, hreg, hetyp, hpoison, hpredNo⟩
          exfalso
          simp [hpredNo] at hpred
      | newRef e1 =>
          have htc' : typecheckNewRef ctx e1 fuel = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckNewRef_structure ctx e1 fuel res htc' with
            ⟨result1, l, htc1, hl, hetyp1, hetyp, hpoison, hpredNo, hmem, htag, hnextLoc, hnextTag, hreg⟩
          exfalso
          simp [hpredNo] at hpred
      | assign e1 e2 =>
          have htc' : typecheckAssign ctx e1 e2 fuel = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckAssign_structure ctx e1 e2 fuel res htc' with
            ⟨result1, result2, ls, htc1, href, htc2, hqt2int, hnextLoc, hnextTag, hreg, hetyp, hpoison, hpredNo⟩
          exfalso
          simp [hpredNo] at hpred
      | seq e1 e2 =>
          have htc' : typecheckSeq ctx e1 e2 fuel = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckSeq_structure ctx e1 e2 fuel res htc' with
            ⟨result1, ctx', htc1, hctx', htc2⟩
          have hlt : fuel - 1 < Nat.succ fuel := Nat.lt_succ_of_le (Nat.sub_le fuel 1)
          have hbounded' : TagBoundedCtx ctx' := by
            rw [hctx']; exact typecheckExpr_preserves_TagBoundedCtx ctx e1 (fuel - 1) result1 htc1 hbounded
          exact ih (fuel - 1) hlt ctx' e2 res htc2 hbounded' hpred
      | vlet x e1 e2 =>
          have htc' : typecheckVlet ctx x e1 e2 fuel = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckVlet_structure ctx x e1 e2 fuel res htc' with
            ⟨result1, result2, ctx', htc1, hctx', htc2, hetyp, hmem, htag, hnextLoc, hnextTag, hreg, hpoison, hpredEq⟩
          have hpred2 : result2.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env := by
            simpa [hpredEq] using hpred
          have hbounded' : TagBoundedCtx ctx' := by
            rw [hctx']
            exact (typecheckExpr_TagBoundedCtx_varEnv_update ctx e1 (fuel - 1) result1 htc1 hbounded x)
          have hnone2 : result2.tagEnv'.get? k = none :=
            ih (fuel - 1) (Nat.lt_succ_of_le (Nat.sub_le fuel 1)) ctx' e2 result2 htc2 hbounded' hpred2
          simpa [htag] using hnone2
      | ite e1 e2 e3 =>
          exfalso
          have htc' : typecheckIf ctx e1 e2 e3 fuel = .ok res := by
            simpa [typecheckExpr] using htc
          have hpredNo : res.qualType.pred = Predicate.noPred :=
            typecheckIf_ok_pred_noPred ctx e1 e2 e3 fuel res htc'
          simp [hpredNo] at hpred
      | var x =>
          have htcVar : typecheckVar ctx x = .ok res := by
            simpa [typecheckExpr] using htc
          exact
            typecheckVar_guardClosure_pred_implies_tag_absent
              ctx x res k arg_name pred_body var_env htcVar hpred
      | deref e1 =>
          have htcD : typecheckDeref ctx e1 fuel = .ok res := by
            simpa [typecheckExpr] using htc
          exact
            typecheckDeref_guardClosure_pred_implies_tag_absent
              ctx e1 fuel res k arg_name pred_body var_env htcD hpred
      | app e1 e2 =>
          have htcA : typecheckApp ctx e1 e2 fuel = .ok res := by
            simpa [typecheckExpr] using htc
          cases fuel with
          | zero =>
              simp [typecheckApp] at htcA
          | succ fuel' =>
              rcases
                  typecheckApp_arrow_structure_full ctx e1 e2 fuel' res (by simpa using htcA)
                with ⟨result2, result1, etyp2, p2, pred2, hq2, htc2, htc1, hcases⟩
              have hb2 := typecheckExpr_preserves_TagBoundedCtx ctx e2 fuel' result2 htc2 hbounded
              have hb1 := typecheckExpr_preserves_TagBoundedCtx _ e1 fuel' result1 htc1 hb2
              have hbounded_r1 : tagEnvBounded result1.tagEnv' result1.nextTag' := hb1.1
              have hClosFull : etypClosuresFullBounded result1.qualType.etyp result1.nextTag' :=
                typecheckExpr_preserves_closureCapturedBounded _ e1 fuel' result1 htc1 hb2.2.1 hb2.2.2
              have hPredM1 : predTagsBoundedInMemEnv result1.memEnv' result1.nextTag' := hb1.2.1.2
              have hmono_r2_r1 : result2.nextTag' ≤ result1.nextTag' :=
                typecheck_normal_nextTag_mono _ e1 fuel' result1 (by simpa [typecheck] using htc1)
              have hArgPred : qtypPredTagBounded ⟨etyp2, joinPoison ctx.pc p2, pred2⟩ result1.nextTag' := by
                have := (typecheckExpr_preserves_predTagsBounded ctx e2 fuel' result2 htc2 hbounded.2.1 hbounded.2.2).2
                rw [hq2] at this; exact qtypPredTagBounded_mono this hmono_r2_r1
              have hArgClos : etypClosuresFullBounded (⟨etyp2, joinPoison ctx.pc p2, pred2⟩ : QTyp).etyp result1.nextTag' := by
                have := typecheckExpr_preserves_closureCapturedBounded ctx e2 fuel' result2 htc2 hbounded.2.1 hbounded.2.2
                rw [hq2] at this; exact etypClosuresFullBounded_mono this hmono_r2_r1
              cases hcases with
              | inl harr =>
                  rcases harr with
                    ⟨st1, st2, p, p1, tcls, results, first, rest,
                      hEtyp1, hPoison1, hNotPure, hTclsNe, hSub,
                      hmap, hresults, hjoin⟩
                  exact
                    typecheckApp_arrow_branch_guardClosure_pred_implies_tag_absent
                      (ctx := ctx) (res := res)
                      (k := k) (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
                      (fuel' := fuel') ih
                      (st1 := st1) (st2 := st2) (p := p) (p1 := p1) (etyp2 := etyp2) (p2 := p2) (pred2 := pred2)
                      (result1 := result1) hbounded_r1 hEtyp1
                      (by rw [hEtyp1] at hClosFull; exact hClosFull)
                      hPredM1 hArgPred hArgClos
                      (results := results) (first := first) (rest := rest)
                      hmap hresults hjoin hpred
              | inr hparr =>
                  rcases hparr with
                    ⟨st1, st2, p, p1, tcls, results, first, rest,
                      hEtyp1, hPoison1, hTclsNe, hSub,
                      hmap, hresults, hjoin⟩
                  exact
                    typecheckApp_parrow_branch_guardClosure_pred_implies_tag_absent
                      (ctx := ctx) (res := res)
                      (k := k) (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
                      (fuel' := fuel') ih
                      (st1 := st1) (st2 := st2) (p := p) (p1 := p1) (etyp2 := etyp2) (p2 := p2) (pred2 := pred2)
                      (result1 := result1) hbounded_r1 hEtyp1
                      (by rw [hEtyp1] at hClosFull; exact hClosFull)
                      hPredM1 hArgPred hArgClos
                      (results := results) (first := first) (rest := rest)
                      hmap hresults hjoin hpred
      | externVal typ poison pred =>
          have htc' : typecheckExternVal ctx typ poison pred = .ok res := by
            simpa [typecheckExpr, typecheck] using htc
          exact typecheckExternVal_guardClosure_pred_implies_tag_absent_of_tagEnvBounded ctx typ poison pred res
            htc' hbounded.1 k arg_name pred_body var_env hpred
      | externFn _ _ _ _ =>
          exfalso
          have htc' := htc
          simp [typecheckExpr, typecheckExternFn] at htc'
          simp [pure, Except.pure] at htc'
          simp [← htc'] at hpred
      | externPfn _ _ _ =>
          exfalso
          have htc' := htc
          simp [typecheckExpr, typecheckExternPfn] at htc'
          simp [pure, Except.pure] at htc'
          simp [← htc'] at hpred

private lemma assign_mem_formula_guardClosure_lookup_implies_rhs_pred
    (ctxᵢ : TypeContext) (res1 res2 res : TypeResult) (ls : LocSet)
    (l : Loc) (qt : QTyp)
    (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
    (hmem :
      res.memEnv' =
        (match Std.ExtTreeSet.toList ls with
        | [l0] =>
            updateMemEnv res2.memEnv' l0
              { etyp := ETyp.int
                poison := joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison)
                pred := if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred }
        | _ =>
            updateLocsetWeak res2.memEnv' ls
              (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
              (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)))
    (hIn : l ∈ ls)
    (hlookup : res.memEnv'.lookup l = some qt)
    (hpred : qt.pred = Predicate.guardClosure k arg_name pred_body var_env) :
    res2.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env := by
  have hlookup_formula :
      (match Std.ExtTreeSet.toList ls with
        | [l0] =>
            updateMemEnv res2.memEnv' l0
              { etyp := ETyp.int
                poison := joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison)
                pred := if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred }
        | _ =>
            updateLocsetWeak res2.memEnv' ls
              (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
              (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)).lookup l = some qt := by
    simpa [hmem] using hlookup
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
          have hlookup_single :
              (updateMemEnv res2.memEnv' x
                { etyp := ETyp.int
                  poison := joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison)
                  pred := if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred }).lookup l = some qt := by
            simpa [hls] using hlookup_formula
          subst hlEq
          simp [updateMemEnv, MemoryTypeEnv.lookup] at hlookup_single
          have hqtEq :
              qt =
                { etyp := ETyp.int
                  poison := joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison)
                  pred := if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred } := by
            simpa using hlookup_single.symm
          have hpred_stored :
              (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred) =
                Predicate.guardClosure k arg_name pred_body var_env := by
            simpa [hqtEq] using hpred
          by_cases hwrite : res1.qualType.poison = true ∨ ctxᵢ.pc = true
          · simp [hwrite] at hpred_stored
          · simpa [hwrite] using hpred_stored
      | cons y ys =>
          have hlookup_weak :
              (updateLocsetWeak res2.memEnv' ls
                (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)).lookup l = some qt := by
            simpa [hls] using hlookup_formula
          unfold updateLocsetWeak at hlookup_weak
          set joined :=
            LocSet.fold ls
              (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison),
                if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)
              (fun (accP, accPred) l0 =>
                match res2.memEnv'.get? l0 with
                | some qt0 => (joinPoison accP qt0.poison, joinPredicates accPred qt0.pred)
                | none => (accP, accPred)) with hjoined
          set finalQt : QTyp := ⟨ETyp.int, joined.1, joined.2⟩ with hfinalQt
          dsimp at hlookup_weak
          unfold LocSet.fold at hlookup_weak
          rw [Std.ExtTreeSet.foldl_eq_foldl_toList] at hlookup_weak
          have hInList : l ∈ ls.toList := (Std.ExtTreeSet.mem_toList).2 hIn
          have hlookup_final :
              (ls.toList.foldl (fun acc l0 => updateMemEnv acc l0 finalQt) res2.memEnv').lookup l = some finalQt :=
            list_fold_updateMemEnv_lookup_eq_of_mem ls.toList res2.memEnv' l finalQt hInList rfl
          have hqtEq : qt = finalQt := by
            have : some qt = some finalQt := by
              calc
                some qt =
                    (ls.toList.foldl (fun acc l0 => updateMemEnv acc l0 finalQt) res2.memEnv').lookup l := by
                      symm
                      exact hlookup_weak
                _ = some finalQt := hlookup_final
            exact Option.some.inj this
          have hjoined_guard :
              joined.2 = Predicate.guardClosure k arg_name pred_body var_env := by
            have hfinal_guard : finalQt.pred = Predicate.guardClosure k arg_name pred_body var_env := by
              simpa [hqtEq] using hpred
            simpa [hfinalQt] using hfinal_guard
          have hjoined_fold :
              ((ls.toList.foldl
                  (fun acc l0 =>
                    match res2.memEnv'.get? l0 with
                    | some qt0 => (joinPoison acc.1 qt0.poison, joinPredicates acc.2 qt0.pred)
                    | none => acc)
                  (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison),
                    if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)).2) =
                Predicate.guardClosure k arg_name pred_body var_env := by
            unfold joined at hjoined_guard
            unfold LocSet.fold at hjoined_guard
            rw [Std.ExtTreeSet.foldl_eq_foldl_toList] at hjoined_guard
            exact hjoined_guard
          have hstored :
              (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred) =
                Predicate.guardClosure k arg_name pred_body var_env :=
            fold_joinPred_guardClosure_init
              res2.memEnv' ls.toList
              (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
              (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)
              hjoined_fold
          by_cases hwrite : res1.qualType.poison = true ∨ ctxᵢ.pc = true
          · simp [hwrite] at hstored
          · simpa [hwrite] using hstored

-- locset_fold_max_succ_ge_of_mem: moved to TypeSafety.lean

private lemma typecheckAssign_result2_lookup_clean_back_of_pc_true
    (ctx : TypeContext) (result1 result2 res : TypeResult) (ls : LocSet)
    (_hInt : result2.qualType.etyp = ETyp.int)
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
    ∀ l qt_out,
      res.memEnv'.lookup l = some qt_out →
      qtypCleanUnder res.regime' qt_out →
      ∃ qt₂, result2.memEnv'.lookup l = some qt₂ ∧ qtypCleanUnder result2.regime' qt₂ := by
  intro l qt_out hlookup_out hclean_out
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
            exact False.elim ((not_qtypCleanUnder_of_poison_true_noPred rfl rfl) hclean_out)
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
            exact False.elim ((not_qtypCleanUnder_of_poison_true_noPred hpoison hpred) hclean_out)
  · have hlookup_eq :
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
    have hlookup₂ : result2.memEnv'.lookup l = some qt_out := by
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
        _ = some qt_out := by simpa [h_mem] using hlookup_out
    have hclean₂ : qtypCleanUnder result2.regime' qt_out := by
      have hclean_inv : qtypCleanUnder (invalidateRegimeDeps result2.regime' result2.tagEnv' ls) qt_out := by
        simpa [h_regime] using hclean_out
      exact qtypCleanUnder_of_monotone
        (invalidateRegimeDeps_monotone result2.regime' result2.tagEnv' ls)
        hclean_inv
    exact ⟨qt_out, hlookup₂, hclean₂⟩

private lemma assign_write_step_preserves_inherited_final_clean_pc_true
    (ctx : TypeContext) (result1 result2 res : TypeResult) (ls : LocSet)
    (cfg2 : Config) (θ : RealizationMap) (a_w : Address) (n : Int)
    (hRef : result1.qualType.etyp = ETyp.ref ls)
    (hvalRef : valueHasETyp θ (Value.loc a_w) result1.qualType.etyp)
    (hθwf : wfRealizationMap θ)
    (hric : runtimeInstantiatesCtx (ctxAfter (updateCtxFromResult ctx result1) result2) cfg2.memory cfg2.varEnv θ)
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
    (hpc : ctx.pc = true) :
    PreservesInheritedFinalCleanLocsOneRun
      (ctxAfter (updateCtxFromResult ctx result1) result2) res
      cfg2.memory (Std.ExtTreeMap.insert cfg2.memory a_w n) θ θ := by
  rcases valueHasETyp_loc_inv hvalRef with ⟨ls', lw, hRef', hwrite, hlwIn'⟩
  have hls : ls' = ls := by
    rw [hRef] at hRef'
    cases hRef'
    rfl
  have hlwIn : lw ∈ ls := by simpa [hls] using hlwIn'
  refine ⟨?_⟩
  intro l qt_in qt_out hlookup_in hlookup_out hclean_out
  have hnotIn : l ∉ ls := by
    intro hIn
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
    cases hlsToList : Std.ExtTreeSet.toList ls with
    | nil =>
        have hInList : l ∈ ls.toList := (Std.ExtTreeSet.mem_toList).2 hIn
        simp [hlsToList] at hInList
    | cons x xs =>
        cases xs with
        | nil =>
            have hlEq : l = x := by
              have hInList : l ∈ ls.toList := (Std.ExtTreeSet.mem_toList).2 hIn
              simpa [hlsToList] using hInList
            subst l
            have hlookup_single :
                (updateMemEnv result2.memEnv' x
                  { etyp := ETyp.int
                    poison := joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison)
                    pred := if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred }).lookup x =
                some qt_out := by
              simpa [hlsToList] using hlookup_formula
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
                  (if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred)).lookup l =
                some qt_out := by
              simpa [hlsToList] using hlookup_formula
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
            have hpoison : qt_out.poison = true := by
              rw [hqt]
              simp [finalQt, joined, hpc]
              unfold LocSet.fold
              rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
              simpa using
                list_fold_joinPoison_first_true result2.memEnv' ls.toList Predicate.noPred
            have hpred : qt_out.pred = Predicate.noPred := by
              rw [hqt]
              simp [finalQt, joined, hpc]
              unfold LocSet.fold
              rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
              simpa using list_fold_joinPredicates_init_noPred result2.memEnv' ls.toList true
            exact (not_qtypCleanUnder_of_poison_true_noPred hpoison hpred) hclean_out
  cases hθ : θ.lookup l with
  | none =>
      exact .both_unrealized hθ hθ
  | some a =>
      have hcontains_a : cfg2.memory.contains a = true := by
        exact (hric.1 l a (by simpa [ctxAfter, updateCtxFromResult] using hθ)).2
      have hmemA : a ∈ cfg2.memory := (ExtTreeMap.contains_iff_mem).1 hcontains_a
      have hisSomeA : cfg2.memory[a]?.isSome = true := (ExtTreeMap.mem_iff_isSome_getElem?).1 hmemA
      cases hlookup_mem_raw : cfg2.memory[a]? with
      | none =>
          simp [hlookup_mem_raw] at hisSomeA
      | some n_old =>
          have hlookup_mem : cfg2.memory.lookup a = some n_old := by
            simp [Memory.lookup, ExtTreeMap.get?_eq_getElem?, hlookup_mem_raw]
          have ha_ne : a ≠ a_w := by
            intro ha
            apply hnotIn
            have hlookup_lw : θ.lookup lw = some a := by simpa [ha] using hwrite
            have hlEq : l = lw := hθwf _ _ _ hθ hlookup_lw
            simpa [hlEq] using hlwIn
          have hlookup_final : Memory.lookup (Std.ExtTreeMap.insert cfg2.memory a_w n) a = some n_old := by
            have hcmp : compare a_w a ≠ Ordering.eq := by
              intro hce
              exact ha_ne ((Nat.compare_eq_eq).1 hce).symm
            simpa [Memory.lookup, Std.ExtTreeMap.getElem?_insert, hcmp] using hlookup_mem
          exact .preserve_value a n_old hθ hlookup_mem hθ hlookup_final

lemma stepFR_assign
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck ctxᵢ (Expr.assign e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR ctxᵢ (Expr.assign e1 e2) res predSat tm := by
  classical
  have htc' : typecheckAssign ctxᵢ e1 e2 (Nat.succ fuel') = .ok res := by
    simpa [typecheck, typecheckExpr] using htc
  obtain ⟨res1, res2, ls, htc1, hRef, htc2, hInt, hNextLoc, hNextTag, hRegime, hEtyp, hPoison, hPred⟩ :=
    typecheckAssign_structure ctxᵢ e1 e2 (Nat.succ fuel') res htc'
  have htc1_expr : typecheckExpr ctxᵢ e1 fuel' = .ok res1 := by
    simpa [Nat.succ_sub_one] using htc1
  have htc2_expr :
      typecheckExpr
         
          { ctxᵢ with
            memEnv := res1.memEnv', tagEnv := res1.tagEnv',
            nextLoc := res1.nextLoc', nextTag := res1.nextTag', regime := res1.regime' }
          e2 fuel' = .ok res2 := by
    simpa [Nat.succ_sub_one] using htc2
  have htc_full := htc'
  simp [typecheckAssign, htc1_expr, htc2_expr, bind, Except.bind, pure, Except.pure] at htc_full
  have htc1' : typecheck ctxᵢ e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  let ctx' : TypeContext := {
    ctxᵢ with
      memEnv := res1.memEnv'
      tagEnv := res1.tagEnv'
      nextLoc := res1.nextLoc'
      nextTag := res1.nextTag'
      regime := res1.regime'
  }
  have htc2' : typecheck ctx' e2 fuel' = .ok res2 := by
    simpa [ctx', typecheck, Nat.succ_sub_one] using htc2
  intro hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hregCtx hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  have hinv₀ := terminatesTo_assign_inv' e1 e2 { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  rcases hinv₀ with ⟨cfg₀1, cfg₀2, a₀w, n₀, ht₀_e1, ht₀_e2, ho₀, hmem₀, hvar₀, hnext₀, hpm₀⟩
  have hinv₁ := terminatesTo_assign_inv' e1 e2 { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  rcases hinv₁ with ⟨cfg₁1, cfg₁2, a₁w, n₁, ht₁_e1, ht₁_e2, ho₁, hmem₁, hvar₁, hnext₁, hpm₁⟩
  have hIH1 := IH fuel' (by simpa using Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 ctxᵢ hwfTm htagBounded res1 htc1'
  have hstep_e1 :=
    hIH1 hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 (Value.loc a₀w) (Value.loc a₁w)
      hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hregCtx hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e1 ht₁_e1
  rcases hstep_e1 with ⟨hresTm1, hstep_e1⟩
  rcases hstep_e1 with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, _hvtyp₀1, _hvtyp₁1, hTm1, hwf1, _htagBounded1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, hregCtx1, hcwr₀1, hcwr₁1, hagree1, hvc₀1, hvc₁1, hres_agree1⟩
  have hwfTm' : wfTagMeaningCtx tm ctx' := by
    simpa [ctx', ctxAfter] using hTm1
  have htagBounded' : TagBoundedCtx ctx' := by
    simpa [ctx', ctxAfter] using _htagBounded1
  have hIH2 := IH fuel' (by simpa using Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e2 ctx' hwfTm' htagBounded' res2 htc2'
  have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀
  have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁
  have hwf_ctx' : wfTypeContext ctx' := by
    simpa [ctx', ctxAfter] using hwf1
  have hric₀1' : runtimeInstantiatesCtx ctx' cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    simpa [ctx', ctxAfter] using hric₀1
  have hric₁1' : runtimeInstantiatesCtx ctx' cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [ctx', ctxAfter] using hric₁1
  have hregCtx1' : regimeConsistentWithCtx ctx' := by
    simpa [ctx', ctxAfter] using hregCtx1
  have hcwr₀1' : consistentWithRegime predSat ctx'.regime ctx' cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    simpa [ctx', ctxAfter] using hcwr₀1
  have hcwr₁1' : consistentWithRegime predSat ctx'.regime ctx' cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [ctx', ctxAfter] using hcwr₁1
  have hagree1' : agreeOnClean predSat ctx'.regime ctx' cfg₀1.memory cfg₀1.varEnv θ₀1 cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [ctx', ctxAfter] using hagree1
  have hmono1 : Regime.monotoneStep ctxᵢ.regime res1.regime' := regime_monotone ctxᵢ e1 fuel' res1 htc1'
  have hpm₀1 : cfg₀1.pureMode = pm := by
    simpa using
      (terminatesTo_preserves_pureMode e1
        { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cfg₀1 (Value.loc a₀w) ht₀_e1)
  have hpm₁1 : cfg₁1.pureMode = pm := by
    simpa using
      (terminatesTo_preserves_pureMode e1
        { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cfg₁1 (Value.loc a₁w) ht₁_e1)
  have hpm_eq : cfg₁1.pureMode = cfg₀1.pureMode := by
    rw [hpm₁1, hpm₀1]
  have hcfg₁1_eq : cfg₁1 = { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode } := by
    cases cfg₁1
    simp only [Config.mk.injEq, true_and]
    exact hpm_eq
  have ht₁_e2' : terminatesTo e2
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode }
      cfg₁2 (Value.num n₁) := by
    rw [← hcfg₁1_eq]
    exact ht₁_e2
  have hwfcf₁1' : wfConfig
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode } := by
    rw [← hcfg₁1_eq]
    exact hwfcf₁1
  have hstep_e2 :=
    hIH2 hpredlaws hwfTm'
      cfg₀1.memory cfg₁1.memory cfg₀1.varEnv cfg₁1.varEnv θ₀1 θ₁1
      cfg₀2 cfg₁2 (Value.num n₀) (Value.num n₁)
      hθ₀1wf hθ₁1wf hwf_ctx' htagBounded' hric₀1' hric₁1' hregCtx1' hcwr₀1' hcwr₁1' hagree1'
      cfg₀1.nextAddr cfg₁1.nextAddr cfg₀1.pureMode hwfcf₀1 hwfcf₁1' ht₀_e2 ht₁_e2'
  rcases hstep_e2 with ⟨hresTm2, hstep_e2⟩
  rcases hstep_e2 with ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, hv₀2, hv₁2, hTm2, hwf2, _htagBounded2, hwfcf₀2, hwfcf₁2, hric₀2, hric₁2, hregCtx2, hcwr₀2, hcwr₁2, hagree2, hvc₀2, hvc₁2, hres_agree2⟩
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    have hnotfun : res.qualType.etyp.isFunctionType = false := by
      simp [hEtyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
    have hguard : qtypGuardDesc? res.qualType = none := by
      simp [qtypGuardDesc?, hPred]
    intro qt' k d hinq hqd
    exact (QTypRespectsTagMeaning_of_nonFunction_noGuard tm res.qualType hnotfun hguard) hinq hqd
  have hθext₀ : wfExtendsMap θ₀ θ₀2 := wfExtendsMap_trans hθext₀1 hθext₀2
  have hθext₁ : wfExtendsMap θ₁ θ₁2 := wfExtendsMap_trans hθext₁1 hθext₁2
  have hwfcf₀_final : wfConfig cf₀ := (wfConfig_preserved (Expr.assign e1 e2) _ cf₀ o₀ ht₀ hwfcfg₀).1
  have hwfcf₁_final : wfConfig cf₁ := (wfConfig_preserved (Expr.assign e1 e2) _ cf₁ o₁ ht₁ hwfcfg₁).1
  have hassign_eq :
      { qualType := { etyp := ETyp.unit, poison := joinPoison ctxᵢ.pc res1.qualType.poison, pred := Predicate.noPred }
        memEnv' :=
          match Std.ExtTreeSet.toList ls with
          | [l] =>
              updateMemEnv res2.memEnv' l
                { etyp := ETyp.int
                  poison := joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison)
                  pred := if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred }
          | _ =>
              updateLocsetWeak res2.memEnv' ls
                (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)
        tagEnv' := invalidateTagDeps res2.tagEnv' ls
        nextLoc' := ls.fold res2.nextLoc' (fun acc l => max acc (l + 1))
        nextTag' := res2.nextTag'
        regime' := invalidateRegimeDeps res2.regime' res2.tagEnv' ls } = res := by
    cases hq1 : res1.qualType with
    | mk etyp1 p1 pred1 =>
        cases hq2 : res2.qualType with
        | mk etyp2 p2 pred2 =>
            have hRef' := hRef
            have hInt' := hInt
            simp [hq1, hq2] at hRef' hInt'
            have htc_assign_simp := htc'
            simp [typecheckAssign, htc1_expr, htc2_expr, hq1, hq2, hRef', hInt', bind, Except.bind, pure, Except.pure] at htc_assign_simp
            simpa [hq1, hq2] using htc_assign_simp
  have hmem_assign := congrArg TypeResult.memEnv' hassign_eq
  have htag_assign := congrArg TypeResult.tagEnv' hassign_eq
  have hmem_res :
      res.memEnv' =
        match Std.ExtTreeSet.toList ls with
        | [l] =>
            updateMemEnv res2.memEnv' l
              { etyp := ETyp.int
                poison := joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison)
                pred := if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred }
        | _ =>
            updateLocsetWeak res2.memEnv' ls
              (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
              (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred) := by
    simpa using hmem_assign.symm
  have htag_res : res.tagEnv' = invalidateTagDeps res2.tagEnv' ls := by
    simpa using htag_assign.symm
  have hmono2_ctx : Regime.monotoneStep ctx'.regime (ctxAfter ctx' res2).regime := by
    exact regime_monotone ctx' e2 fuel' res2 htc2'
  have hmono2 : Regime.monotoneStep res1.regime' res2.regime' := by
    simpa [ctx', ctxAfter] using hmono2_ctx
  have hmono12 : Regime.monotoneStep ctxᵢ.regime res2.regime' := regimeMonotone_trans hmono1 hmono2
  -- Assignment-specific transport from IH2 post-state to final updated states/context.
  have hpost_transport :
      wfTagMeaningCtx tm (ctxAfter ctxᵢ res) ∧
      wfTypeContext (ctxAfter ctxᵢ res) ∧
      runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 ∧
      runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 ∧
      regimeConsistentWithCtx (ctxAfter ctxᵢ res) ∧
      consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 ∧
      consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 ∧
      agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁2 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · let storedPred : Predicate :=
        if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred
      let storedQt : QTyp :=
        { etyp := ETyp.int
          poison := joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison)
          pred := storedPred }
      have hstored_pred_respects : PredRespectsTagMeaning tm storedPred := by
        intro k arg_name pred_body var_env hpred
        by_cases hwrite : res1.qualType.poison = true ∨ ctxᵢ.pc = true
        · simp [storedPred, hwrite] at hpred
        · have hpred_res2 :
            res2.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env := by
            simpa [storedPred, hwrite] using hpred
          have hqd2 :
              qtypGuardDesc? res2.qualType =
                some (k, { argName := arg_name, body := pred_body, capEnv := var_env }) := by
            simp [qtypGuardDesc?, hpred_res2]
          exact hresTm2 (QTypInQTyp.self res2.qualType) hqd2
      have hstored_qtyp : QTypRespectsTagMeaning tm storedQt := by
        unfold storedQt
        exact
          QTypRespectsTagMeaning_int_of_predRespects
            tm
            (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
            storedPred
            hstored_pred_respects
      have hEnvTm_res2 : EnvRespectsTagMeaning tm ctxᵢ.varEnv res2.memEnv' := by
        simpa [wfTagMeaningCtx, ctxAfter, ctx'] using hTm2
      have hEnvTm_res : EnvRespectsTagMeaning tm ctxᵢ.varEnv res.memEnv' := by
        rw [hmem_res]
        cases hls : Std.ExtTreeSet.toList ls with
        | nil =>
            simp
            exact
              EnvRespectsTagMeaning_updateLocsetWeak
                tm ctxᵢ.varEnv res2.memEnv' ls
                (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                storedPred
                hEnvTm_res2
                hstored_pred_respects
        | cons x xs =>
            cases xs with
            | nil =>
                simp
                exact
                  EnvRespectsTagMeaning_updateMemEnv
                    tm ctxᵢ.varEnv res2.memEnv' x storedQt (by simp [storedQt]) hEnvTm_res2 hstored_qtyp
            | cons y ys =>
                simp
                exact
                  EnvRespectsTagMeaning_updateLocsetWeak
                    tm ctxᵢ.varEnv res2.memEnv' ls
                    (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                    storedPred
                    hEnvTm_res2
                    hstored_pred_respects
      exact wfTagMeaningCtx_ctxAfter tm ctxᵢ res hEnvTm_res
    · simp only [wfTypeContext, ctxAfter]
      have hmono_res : ctxᵢ.nextLoc ≤ res.nextLoc' :=
        typecheck_nextLoc_mono ctxᵢ (Expr.assign e1 e2) (fuel' + 2) res htc
      refine ⟨?_, varEnvRefLocsBounded_mono hwf.2.1 hmono_res,
               varEnvClosuresCapturedRefLocsBounded_mono hwf.2.2 hmono_res⟩
      intro l hcontains
      have hcontains' : res.memEnv'.contains l = true := hcontains
      have hsplit : res2.memEnv'.contains l = true ∨ l ∈ ls := by
        rw [hmem_res] at hcontains'
        exact assign_memEnv_formula_contains_eq_or_mem
          res2.memEnv' ls
          (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
          (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)
          l hcontains'
      cases hsplit with
      | inl hOld =>
          have hOldCtx : (ctxAfter ctx' res2).memEnv.contains l := by
            simpa [ctxAfter, ctx'] using hOld
          have hltOld' : l < (ctxAfter ctx' res2).nextLoc := hwf2.1 l hOldCtx
          have hltOld : l < res2.nextLoc' := by
            simpa [ctxAfter, ctx'] using hltOld'
          have hbase : res2.nextLoc' ≤ res.nextLoc' := by
            rw [hNextLoc]
            unfold LocSet.fold
            rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
            exact list_fold_max_ge_init ls.toList res2.nextLoc'
          exact Nat.lt_of_lt_of_le hltOld hbase
      | inr hIn =>
          have hle : l + 1 ≤ res.nextLoc' := by
            rw [hNextLoc]
            exact locset_fold_max_succ_ge_of_mem ls res2.nextLoc' l hIn
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self l) hle
    · unfold runtimeInstantiatesCtx at hric₀2 ⊢
      rcases hric₀2 with ⟨hmem₂, hvars₂⟩
      constructor
      · intro l a hlookup
        have hmem_old := hmem₂ l a hlookup
        constructor
        · have h_old_contains : res2.memEnv'.contains l = true := by
            simpa [ctxAfter, ctx'] using hmem_old.1
          have h_new_contains : res.memEnv'.contains l = true := by
            rw [hmem_res]
            exact assign_memEnv_formula_contains_of_contains
              res2.memEnv' ls
              (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
              (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)
              l h_old_contains
          simpa [ctxAfter] using h_new_contains
        · have hμ_old : cfg₀2.memory.contains a = true := by
            simpa using hmem_old.2
          have hμ_new : cf₀.memory.contains a = true := by
            rw [hmem₀, Std.ExtTreeMap.contains_insert]
            simp [hμ_old]
          simpa using hμ_new
      · intro x qt hlookup
        have hlookup_ctx2 : (ctxAfter ctx' res2).varEnv.lookup x = some qt := by
          simpa [ctxAfter, ctx'] using hlookup
        obtain ⟨v, hvlookup, hvtyp⟩ := hvars₂ hlookup_ctx2
        refine ⟨v, ?_, hvtyp⟩
        simpa [hvar₀] using hvlookup
    · unfold runtimeInstantiatesCtx at hric₁2 ⊢
      rcases hric₁2 with ⟨hmem₂, hvars₂⟩
      constructor
      · intro l a hlookup
        have hmem_old := hmem₂ l a hlookup
        constructor
        · have h_old_contains : res2.memEnv'.contains l = true := by
            simpa [ctxAfter, ctx'] using hmem_old.1
          have h_new_contains : res.memEnv'.contains l = true := by
            rw [hmem_res]
            exact assign_memEnv_formula_contains_of_contains
              res2.memEnv' ls
              (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
              (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)
              l h_old_contains
          simpa [ctxAfter] using h_new_contains
        · have hμ_old : cfg₁2.memory.contains a = true := by
            simpa using hmem_old.2
          have hμ_new : cf₁.memory.contains a = true := by
            rw [hmem₁, Std.ExtTreeMap.contains_insert]
            simp [hμ_old]
          simpa using hμ_new
      · intro x qt hlookup
        have hlookup_ctx2 : (ctxAfter ctx' res2).varEnv.lookup x = some qt := by
          simpa [ctxAfter, ctx'] using hlookup
        obtain ⟨v, hvlookup, hvtyp⟩ := hvars₂ hlookup_ctx2
        refine ⟨v, ?_, hvtyp⟩
        simpa [hvar₁] using hvlookup
    · unfold regimeConsistentWithCtx at hregCtx2 ⊢
      have htag_res2_R2 : tagEnvConsistentWithRegime res2.tagEnv' res2.regime' := by
        simpa [ctxAfter, ctx'] using hregCtx2
      have htag_inv :
          tagEnvConsistentWithRegime (invalidateTagDeps res2.tagEnv' ls)
            (invalidateRegimeDeps res2.regime' res2.tagEnv' ls) :=
        tagEnvConsistentWithRegime_invalidateRegimeDeps res2.tagEnv' res2.regime' ls htag_res2_R2
      simpa [ctxAfter, htag_res, hRegime] using htag_inv
    · unfold consistentWithRegime
      constructor
      · intro l qt k hlookup hguard hkR
        have hlookup_res : res.memEnv'.lookup l = some qt := by
          simpa [ctxAfter] using hlookup
        have hcontains_res : res.memEnv'.contains l = true := by
          have h := memEnv_contains_of_lookup_some res.memEnv' l qt hlookup_res
          exact (Std.ExtTreeMap.contains_iff_mem).2 h
        have hcontains_formula :
            (match Std.ExtTreeSet.toList ls with
              | [l0] =>
                  updateMemEnv res2.memEnv' l0
                    { etyp := ETyp.int
                      poison := joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison)
                      pred := if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred }
              | _ =>
                  updateLocsetWeak res2.memEnv' ls
                    (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                    (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)).contains l = true := by
          simpa [hmem_res] using hcontains_res
        have hsplit : res2.memEnv'.contains l = true ∨ l ∈ ls := by
          exact assign_memEnv_formula_contains_eq_or_mem
            res2.memEnv' ls
            (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
            (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)
            l hcontains_formula
        have hkR_res : res.regime'.lookup? k ≠ none := by
          simpa [ctxAfter] using hkR
        have hkR_ctxi : ctxᵢ.regime.lookup? k ≠ none := by
          have hkR_res' :
              (invalidateRegimeDeps res2.regime' res2.tagEnv' ls).lookup? k ≠ none := by
            simpa [hRegime] using hkR_res
          have hkR_res2 : res2.regime'.lookup? k ≠ none :=
            invalidateRegimeDeps_lookup_ne_none_implies_original_ne_none
              res2.regime' res2.tagEnv' ls k hkR_res'
          exact hmono12.2 k hkR_res2
        cases hsplit with
        | inl hOld =>
            by_cases hIn : l ∈ ls
            · -- Updated location that also existed in the old environment.
              -- This is the hard assignment-specific branch.
              cases hpred : qt.pred with
              | noPred =>
                  simp [qtypGuardTag, hpred] at hguard
              | guardOnly k' =>
                  exact locsRegime.guardOnly_ok (l, qt) k' hpred
              | guardClosure k' arg_name pred_body var_env =>
                  exfalso
                  have hk_eq : k' = k := by
                    have : some k' = some k := by
                      calc
                        some k' = qtypGuardTag qt := by simp [qtypGuardTag, hpred]
                        _ = some k := hguard
                    exact Option.some.inj this
                  have hpred_res2 :
                      res2.qualType.pred = Predicate.guardClosure k' arg_name pred_body var_env := by
                    exact
                      assign_mem_formula_guardClosure_lookup_implies_rhs_pred
                        (ctxᵢ := ctxᵢ) (res1 := res1) (res2 := res2) (res := res)
                        (ls := ls) (l := l) (qt := qt)
                        (k := k') (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
                        hmem_res hIn hlookup_res hpred
                  have hnone : res2.tagEnv'.get? k' = none := by
                    exact
                      guardClosure_pred_implies_tag_absent
                        (ctx := { ctxᵢ with
                          memEnv := res1.memEnv'
                          tagEnv := res1.tagEnv'
                          nextLoc := res1.nextLoc'
                          nextTag := res1.nextTag'
                          regime := res1.regime' })
                        (e := e2) (fuel := fuel') (res := res2)
                        (k := k') (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
                        htc2_expr htagBounded' hpred_res2
                  have htagInvalid :
                      ∀ tv, res2.tagEnv'.get? k' = some tv → tv.deps.any ls.contains = true := by
                    intro tv hget'
                    rw [hnone] at hget'
                    cases hget'
                  have hnoneInv :
                      (invalidateRegimeDeps res2.regime' res2.tagEnv' ls).lookup? k' = none :=
                    assign_updated_new_guardClosure_implies_invalidated_regime_none
                      res2.regime' res2.tagEnv' ls k' htagInvalid
                  have hkR_inv : (invalidateRegimeDeps res2.regime' res2.tagEnv' ls).lookup? k' ≠ none := by
                    have hkR_res_k : res.regime'.lookup? k ≠ none := by
                      simpa [ctxAfter] using hkR
                    have hkR_res_k' : res.regime'.lookup? k' ≠ none := by
                      simpa [hk_eq] using hkR_res_k
                    simpa [hRegime] using hkR_res_k'
                  exact hkR_inv hnoneInv
            · -- Unchanged location: recover old lookup and reuse old consistency shape.
              have hlookup_ctx2 : (ctxAfter ctx' res2).memEnv.lookup l = some qt := by
                have hlookup_formula :
                    (match Std.ExtTreeSet.toList ls with
                      | [l0] =>
                          updateMemEnv res2.memEnv' l0
                            { etyp := ETyp.int
                              poison := joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison)
                              pred := if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred }
                      | _ =>
                          updateLocsetWeak res2.memEnv' ls
                            (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                            (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)).lookup l = some qt := by
                  simpa [hmem_res] using hlookup_res
                have hlookup_res2 : res2.memEnv'.lookup l = some qt := by
                  have hlookup_eq :
                      (match Std.ExtTreeSet.toList ls with
                        | [l0] =>
                            updateMemEnv res2.memEnv' l0
                              { etyp := ETyp.int
                                poison := joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison)
                                pred := if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred }
                        | _ =>
                            updateLocsetWeak res2.memEnv' ls
                              (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                              (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)).lookup l =
                        res2.memEnv'.lookup l :=
                    assign_memEnv_formula_lookup_eq_of_not_mem
                      res2.memEnv' ls
                      (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                      (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)
                      l hIn
                  rwa [hlookup_eq] at hlookup_formula
                simpa [ctxAfter, ctx'] using hlookup_res2
              -- We still need a source-regime witness for `res2.regime'`.
              have hkR_res2 : res2.regime'.lookup? k ≠ none := by
                have hkR_inv : (invalidateRegimeDeps res2.regime' res2.tagEnv' ls).lookup? k ≠ none := by
                  simpa [hRegime] using hkR_res
                exact
                  invalidateRegimeDeps_lookup_ne_none_implies_original_ne_none
                    res2.regime' res2.tagEnv' ls k hkR_inv
              have hloc2 := hcwr₀2.1 l qt k hlookup_ctx2 hguard hkR_res2
              cases hloc2 with
              | noPred_ok hnp =>
                  exfalso
                  simp [hnp] at hguard
              | guardOnly_ok k' hgo =>
                  exact locsRegime.guardOnly_ok (l, qt) k' hgo
              | withPred_ok k' arg_name pred_body var_env a n b hclos hreg hreal hmem hcons =>
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
                  have hreg_res2 : res2.regime'.lookup? k = some b := by
                    simpa [ctxAfter, ctx', hk_eq] using hreg
                  have hk_ctxi : ctxᵢ.regime.lookup? k = some b := by
                    have hk_ctxi_not_none : ctxᵢ.regime.lookup? k ≠ none := by
                      exact hmono12.2 k (by simp [hreg_res2])
                    cases hk0 : ctxᵢ.regime.lookup? k with
                    | none =>
                        exact (hk_ctxi_not_none hk0).elim
                    | some b0 =>
                        have hmono_keep : res2.regime'.lookup? k = some b0 ∨ res2.regime'.lookup? k = none :=
                          hmono12.1 k b0 hk0
                        cases hmono_keep with
                        | inl hk_keep =>
                            have hb : b0 = b := by
                              have : some b0 = some b := hk_keep.symm.trans hreg_res2
                              exact Option.some.inj this
                            simp [hb] at hk0 ⊢
                        | inr hk_none =>
                            simp [hk_none] at hreg_res2
                  have hkeep : (invalidateTagDeps res2.tagEnv' ls).contains k = true :=
                    invalidateRegimeDeps_survives_of_lookup_ne_none res2.regime' res2.tagEnv' ls k
                      (by simpa [hRegime] using hkR_res)
                  have hlookup_eq :
                      (ctxAfter ctxᵢ res).regime.lookup? k = res2.regime'.lookup? k := by
                    simpa [ctxAfter, hRegime] using
                      invalidateRegimeDeps_lookup_eq_lookup_of_surviving_tag res2.regime' res2.tagEnv' ls k hkeep
                  have hregR : (ctxAfter ctxᵢ res).regime.lookup? k' = some b := by
                    calc
                      (ctxAfter ctxᵢ res).regime.lookup? k' = (ctxAfter ctxᵢ res).regime.lookup? k := by simp [hk_eq]
                      _ = res2.regime'.lookup? k := hlookup_eq
                      _ = some b := hreg_res2
                  have hreal' : θ₀2.lookup (l, qt).1 = some a := by
                    simpa using hreal
                  have hvloc₀ : valueHasETyp θ₀1 (Value.loc a₀w) (ETyp.ref ls) := by
                    simpa [hRef] using _hvtyp₀1
                  have hne_a : a ≠ a₀w := by
                    intro haeq
                    cases hvloc₀ with
                    | loc hlookup_w hin_w =>
                        have hlookup_w' : θ₀2.lookup _ = some a₀w := hθext₀2.1 _ _ hlookup_w
                        have hlookup_l : θ₀2.lookup l = some a₀w := by
                          simpa [haeq] using hreal'
                        have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀1wf
                        have hl_eq : l = _ := hθ₀2wf _ _ _ hlookup_l hlookup_w'
                        have : l ∈ ls := by simpa [hl_eq] using hin_w
                        exact hIn this
                  have hcmp : compare a₀w a ≠ Ordering.eq := by
                    intro hce
                    have : a₀w = a := (Nat.compare_eq_eq).1 hce
                    exact hne_a this.symm
                  have hmem' : cf₀.memory.lookup a = some n := by
                    rw [hmem₀]
                    have : cfg₀2.memory.lookup a = some n := hmem
                    simpa [Memory.lookup, Std.ExtTreeMap.getElem?_insert, hcmp] using this
                  have hPredSat_mem :
                      ∀ (k : Tag) (μ μ' : Memory) (v : Value), predSat k μ v ↔ predSat k μ' v := by
                    intro k μ μ' v
                    exact predSat_mem_noPred_compat hpredlaws θ₀2 k μ μ' v
                  have hqtypPredHolds_mem :
                      ∀ (qt : QTyp) (v : Value) (μ μ' : Memory),
                        qtypPredHolds predSat qt μ v ↔ qtypPredHolds predSat qt μ' v := by
                    intro qt v μ μ'
                    constructor
                    · intro hholds
                      cases hholds with
                      | noPred_ok hpred =>
                          exact qtypPredHolds.noPred_ok hpred
                      | guardClosure_ok hpred hSat =>
                          exact qtypPredHolds.guardClosure_ok hpred ((hPredSat_mem _ μ μ' v).1 hSat)
                      | guardOnly_ok hpred hSat =>
                          exact qtypPredHolds.guardOnly_ok hpred ((hPredSat_mem _ μ μ' v).1 hSat)
                    · intro hholds
                      cases hholds with
                      | noPred_ok hpred =>
                          exact qtypPredHolds.noPred_ok hpred
                      | guardClosure_ok hpred hSat =>
                          exact qtypPredHolds.guardClosure_ok hpred ((hPredSat_mem _ μ μ' v).2 hSat)
                      | guardOnly_ok hpred hSat =>
                          exact qtypPredHolds.guardOnly_ok hpred ((hPredSat_mem _ μ μ' v).2 hSat)
                  have hcons' :
                      (b = true → qtypPredHolds predSat qt cf₀.memory (Value.num n)) ∧
                      (b = false → ¬ qtypPredHolds predSat qt cf₀.memory (Value.num n)) := by
                    constructor
                    · intro hbtrue
                      have hholds_old := hcons.1 hbtrue
                      exact (hqtypPredHolds_mem qt (Value.num n) cfg₀2.memory cf₀.memory).1 hholds_old
                    · intro hbfalse hholds_new
                      have hholds_old :=
                        (hqtypPredHolds_mem qt (Value.num n) cfg₀2.memory cf₀.memory).2 hholds_new
                      exact (hcons.2 hbfalse) hholds_old
                  exact locsRegime.withPred_ok (l, qt) k' arg_name pred_body var_env a n b hclos hregR hreal' hmem' hcons'
        | inr _hIn =>
            -- Updated location branch.
            cases hpred : qt.pred with
            | noPred =>
                simp [qtypGuardTag, hpred] at hguard
            | guardOnly k' =>
                exact locsRegime.guardOnly_ok (l, qt) k' hpred
            | guardClosure k' arg_name pred_body var_env =>
                exfalso
                have hk_eq : k' = k := by
                  have : some k' = some k := by
                    calc
                      some k' = qtypGuardTag qt := by simp [qtypGuardTag, hpred]
                      _ = some k := hguard
                  exact Option.some.inj this
                have hpred_res2 :
                    res2.qualType.pred = Predicate.guardClosure k' arg_name pred_body var_env := by
                  exact
                    assign_mem_formula_guardClosure_lookup_implies_rhs_pred
                      (ctxᵢ := ctxᵢ) (res1 := res1) (res2 := res2) (res := res)
                      (ls := ls) (l := l) (qt := qt)
                      (k := k') (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
                      hmem_res _hIn hlookup_res hpred
                have hnone : res2.tagEnv'.get? k' = none := by
                  exact
                    guardClosure_pred_implies_tag_absent
                      (ctx := { ctxᵢ with
                        memEnv := res1.memEnv'
                        tagEnv := res1.tagEnv'
                        nextLoc := res1.nextLoc'
                        nextTag := res1.nextTag'
                        regime := res1.regime' })
                      (e := e2) (fuel := fuel') (res := res2)
                      (k := k') (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
                      htc2_expr htagBounded' hpred_res2
                have htagInvalid :
                    ∀ tv, res2.tagEnv'.get? k' = some tv → tv.deps.any ls.contains = true := by
                  intro tv hget'
                  rw [hnone] at hget'
                  cases hget'
                have hnoneInv :
                    (invalidateRegimeDeps res2.regime' res2.tagEnv' ls).lookup? k' = none :=
                  assign_updated_new_guardClosure_implies_invalidated_regime_none
                    res2.regime' res2.tagEnv' ls k' htagInvalid
                have hkR_inv : (invalidateRegimeDeps res2.regime' res2.tagEnv' ls).lookup? k' ≠ none := by
                  have hkR_res_k : res.regime'.lookup? k ≠ none := by
                    simpa [ctxAfter] using hkR
                  have hkR_res_k' : res.regime'.lookup? k' ≠ none := by
                    simpa [hk_eq] using hkR_res_k
                  simpa [hRegime] using hkR_res_k'
                exact hkR_inv hnoneInv
      · constructor
        · intro x qt k hlookup hguard hkR
          have hlookup_ctxi : ctxᵢ.varEnv.lookup x = some qt := by
            simpa [ctxAfter] using hlookup
          have hkR_res : res.regime'.lookup? k ≠ none := by
            simpa [ctxAfter] using hkR
          have hkR_ctxi : ctxᵢ.regime.lookup? k ≠ none := by
            have hkR_res' :
                (invalidateRegimeDeps res2.regime' res2.tagEnv' ls).lookup? k ≠ none := by
              simpa [hRegime] using hkR_res
            have hkR_res2 : res2.regime'.lookup? k ≠ none :=
              invalidateRegimeDeps_lookup_ne_none_implies_original_ne_none
                res2.regime' res2.tagEnv' ls k hkR_res'
            exact hmono12.2 k hkR_res2
          have hvars := hcwr₀.2.1 x qt k hlookup_ctxi hguard hkR_ctxi
          have hPredSat_mem :
              ∀ (k : Tag) (μ μ' : Memory) (v : Value), predSat k μ v ↔ predSat k μ' v := by
            intro k μ μ' v
            exact predSat_mem_noPred_compat hpredlaws θ₀2 k μ μ' v
          have hqtypPredHolds_mem :
              ∀ (qt : QTyp) (v : Value) (μ μ' : Memory),
                qtypPredHolds predSat qt μ v ↔ qtypPredHolds predSat qt μ' v := by
            intro qt v μ μ'
            constructor
            · intro h
              cases h with
              | noPred_ok hpred =>
                  exact qtypPredHolds.noPred_ok hpred
              | guardClosure_ok hpred hSat =>
                  exact qtypPredHolds.guardClosure_ok hpred ((hPredSat_mem _ μ μ' v).1 hSat)
              | guardOnly_ok hpred hSat =>
                  exact qtypPredHolds.guardOnly_ok hpred ((hPredSat_mem _ μ μ' v).1 hSat)
            · intro h
              cases h with
              | noPred_ok hpred =>
                  exact qtypPredHolds.noPred_ok hpred
              | guardClosure_ok hpred hSat =>
                  exact qtypPredHolds.guardClosure_ok hpred ((hPredSat_mem _ μ μ' v).2 hSat)
              | guardOnly_ok hpred hSat =>
                  exact qtypPredHolds.guardOnly_ok hpred ((hPredSat_mem _ μ μ' v).2 hSat)
          have hvar_cf₀ : cf₀.varEnv = ρ₀ := by
            rcases ht₀ with ⟨fuel₀w, verbose₀w, hpure₀w⟩
            have hvar_eq :=
                beval_preserves_varEnv (e1.assign e2) fuel₀w verbose₀w
                { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀
                hpure₀w
            simpa using hvar_eq.symm
          cases hvars with
          | noPred_ok hnp =>
              exact varsRegime.noPred_ok (x, qt) hnp
          | guardOnly_ok k' hgo =>
              exact varsRegime.guardOnly_ok (x, qt) k' hgo
          | withPred_ok k' arg_name pred_body var_env v b hclos hreg hvar hcons =>
              have hk_eq : k' = k := by
                have hclos' : qt.pred = Predicate.guardClosure k' arg_name pred_body var_env := by
                  simpa using hclos
                have hguard' : qtypGuardTag qt = some k' := by
                  simp [qtypGuardTag, hclos']
                have : some k' = some k := by
                  simpa [hguard'] using hguard
                exact Option.some.inj this
              subst k'
              have hkR_res' :
                  (invalidateRegimeDeps res2.regime' res2.tagEnv' ls).lookup? k ≠ none := by
                simpa [hRegime] using hkR_res
              have hkR_res2 : res2.regime'.lookup? k ≠ none :=
                invalidateRegimeDeps_lookup_ne_none_implies_original_ne_none
                  res2.regime' res2.tagEnv' ls k hkR_res'
              have hreg_res2 : res2.regime'.lookup? k = some b := by
                have hmono_keep : res2.regime'.lookup? k = some b ∨ res2.regime'.lookup? k = none :=
                  hmono12.1 k b hreg
                cases hmono_keep with
                | inl hk_keep =>
                    exact hk_keep
                | inr hk_none =>
                    exact (hkR_res2 hk_none).elim
              have hkeep : (invalidateTagDeps res2.tagEnv' ls).contains k = true :=
                invalidateRegimeDeps_survives_of_lookup_ne_none res2.regime' res2.tagEnv' ls k hkR_res'
              have hlookup_eq :
                  (ctxAfter ctxᵢ res).regime.lookup? k = res2.regime'.lookup? k := by
                simpa [ctxAfter, hRegime] using
                  invalidateRegimeDeps_lookup_eq_lookup_of_surviving_tag res2.regime' res2.tagEnv' ls k hkeep
              have hregR : (ctxAfter ctxᵢ res).regime.lookup? k = some b := by
                calc
                  (ctxAfter ctxᵢ res).regime.lookup? k = res2.regime'.lookup? k := hlookup_eq
                  _ = some b := hreg_res2
              have hvar' : cf₀.varEnv.lookup x = some v := by
                simpa [hvar_cf₀] using hvar
              have hcons' :
                  (b = true → qtypPredHolds predSat qt cf₀.memory v) ∧
                  (b = false → ¬ qtypPredHolds predSat qt cf₀.memory v) := by
                constructor
                · intro hbtrue
                  have hholds_old := hcons.1 hbtrue
                  exact (hqtypPredHolds_mem qt v μ₀ cf₀.memory).1 hholds_old
                · intro hbfalse hholds_new
                  have hholds_old := (hqtypPredHolds_mem qt v μ₀ cf₀.memory).2 hholds_new
                  exact (hcons.2 hbfalse) hholds_old
              exact varsRegime.withPred_ok (x, qt) k arg_name pred_body var_env v b hclos hregR hvar' hcons'
        · intro x qt v hlookup hlookup_v
          have hlookup_ctx2 : (ctxAfter ctx' res2).varEnv.lookup x = some qt := by
            simpa [ctxAfter, ctx'] using hlookup
          have hlookup_v_ctx2 : cfg₀2.varEnv.lookup x = some v := by
            simpa [hvar₀] using hlookup_v
          have hcap_ctx2 :
              closureCapturedVarsRegime predSat (ctxAfter ctx' res2).regime qt cfg₀2.memory θ₀2 v :=
            hcwr₀2.2.2 x qt v hlookup_ctx2 hlookup_v_ctx2
          have hmono_res2_to_final :
              Regime.monotoneStep (ctxAfter ctx' res2).regime (ctxAfter ctxᵢ res).regime := by
            simpa [ctxAfter, ctx', hRegime] using
              invalidateRegimeDeps_monotone res2.regime' res2.tagEnv' ls
          have hcap_final_regime :
              closureCapturedVarsRegime predSat (ctxAfter ctxᵢ res).regime qt cfg₀2.memory θ₀2 v :=
            closureCapturedVarsRegime_monotone hmono_res2_to_final hcap_ctx2
          have hpred_compat :
              ∀ (qt' : QTyp) (v' : Value),
                qtypPredHolds predSat qt' cfg₀2.memory v' ↔
                  qtypPredHolds predSat qt' cf₀.memory v' :=
            qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₀2 cfg₀2.memory cf₀.memory
          exact closureCapturedVarsRegime_transport_μ hpred_compat hcap_final_regime
    · unfold consistentWithRegime
      constructor
      · intro l qt k hlookup hguard hkR
        have hkR_res : res.regime'.lookup? k ≠ none := by
          simpa [ctxAfter] using hkR
        have hkR_ctxi : ctxᵢ.regime.lookup? k ≠ none := by
          have hkR_res' :
              (invalidateRegimeDeps res2.regime' res2.tagEnv' ls).lookup? k ≠ none := by
            simpa [hRegime] using hkR_res
          have hkR_res2 : res2.regime'.lookup? k ≠ none :=
            invalidateRegimeDeps_lookup_ne_none_implies_original_ne_none
              res2.regime' res2.tagEnv' ls k hkR_res'
          exact hmono12.2 k hkR_res2
        have hlookup_res : res.memEnv'.lookup l = some qt := by
          simpa [ctxAfter] using hlookup
        have hcontains_res : res.memEnv'.contains l = true := by
          have h := memEnv_contains_of_lookup_some res.memEnv' l qt hlookup_res
          exact (Std.ExtTreeMap.contains_iff_mem).2 h
        have hcontains_formula :
            (match Std.ExtTreeSet.toList ls with
              | [l0] =>
                  updateMemEnv res2.memEnv' l0
                    { etyp := ETyp.int
                      poison := joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison)
                      pred := if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred }
              | _ =>
                  updateLocsetWeak res2.memEnv' ls
                    (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                    (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)).contains l = true := by
          simpa [hmem_res] using hcontains_res
        have hsplit : res2.memEnv'.contains l = true ∨ l ∈ ls := by
          exact assign_memEnv_formula_contains_eq_or_mem
            res2.memEnv' ls
            (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
            (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)
            l hcontains_formula
        cases hsplit with
        | inl hOld =>
            by_cases hIn : l ∈ ls
            · -- Updated location that also existed in the old environment.
              -- This is the hard assignment-specific branch.
              cases hpred : qt.pred with
              | noPred =>
                  exfalso
                  simp [qtypGuardTag, hpred] at hguard
              | guardOnly k' =>
                  exact locsRegime.guardOnly_ok (l, qt) k' hpred
              | guardClosure k' arg_name pred_body var_env =>
                  exfalso
                  have hk_eq : k' = k := by
                    have : some k' = some k := by
                      calc
                        some k' = qtypGuardTag qt := by simp [qtypGuardTag, hpred]
                        _ = some k := hguard
                    exact Option.some.inj this
                  have hpred_res2 :
                      res2.qualType.pred = Predicate.guardClosure k' arg_name pred_body var_env := by
                    exact
                      assign_mem_formula_guardClosure_lookup_implies_rhs_pred
                        (ctxᵢ := ctxᵢ) (res1 := res1) (res2 := res2) (res := res)
                        (ls := ls) (l := l) (qt := qt)
                        (k := k') (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
                        hmem_res hIn hlookup_res hpred
                  have hnone : res2.tagEnv'.get? k' = none := by
                    exact
                      guardClosure_pred_implies_tag_absent
                        (ctx := { ctxᵢ with
                          memEnv := res1.memEnv'
                          tagEnv := res1.tagEnv'
                          nextLoc := res1.nextLoc'
                          nextTag := res1.nextTag'
                          regime := res1.regime' })
                        (e := e2) (fuel := fuel') (res := res2)
                        (k := k') (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
                        htc2_expr htagBounded' hpred_res2
                  have htagInvalid :
                      ∀ tv, res2.tagEnv'.get? k' = some tv → tv.deps.any ls.contains = true := by
                    intro tv hget'
                    rw [hnone] at hget'
                    cases hget'
                  have hnoneInv :
                      (invalidateRegimeDeps res2.regime' res2.tagEnv' ls).lookup? k' = none :=
                    assign_updated_new_guardClosure_implies_invalidated_regime_none
                      res2.regime' res2.tagEnv' ls k' htagInvalid
                  have hkR_inv : (invalidateRegimeDeps res2.regime' res2.tagEnv' ls).lookup? k' ≠ none := by
                    have hkR_res_k : res.regime'.lookup? k ≠ none := by
                      simpa [ctxAfter] using hkR
                    have hkR_res_k' : res.regime'.lookup? k' ≠ none := by
                      simpa [hk_eq] using hkR_res_k
                    simpa [hRegime] using hkR_res_k'
                  exact hkR_inv hnoneInv
            · -- Unchanged location: recover old lookup and reuse old consistency shape.
              have hlookup_ctx2 : (ctxAfter ctx' res2).memEnv.lookup l = some qt := by
                have hlookup_formula :
                    (match Std.ExtTreeSet.toList ls with
                      | [l0] =>
                          updateMemEnv res2.memEnv' l0
                            { etyp := ETyp.int
                              poison := joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison)
                              pred := if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred }
                      | _ =>
                          updateLocsetWeak res2.memEnv' ls
                            (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                            (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)).lookup l = some qt := by
                  simpa [hmem_res] using hlookup_res
                have hlookup_res2 : res2.memEnv'.lookup l = some qt := by
                  have hlookup_eq :
                      (match Std.ExtTreeSet.toList ls with
                        | [l0] =>
                            updateMemEnv res2.memEnv' l0
                              { etyp := ETyp.int
                                poison := joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison)
                                pred := if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred }
                        | _ =>
                            updateLocsetWeak res2.memEnv' ls
                              (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                              (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)).lookup l =
                        res2.memEnv'.lookup l :=
                    assign_memEnv_formula_lookup_eq_of_not_mem
                      res2.memEnv' ls
                      (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                      (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)
                      l hIn
                  rwa [hlookup_eq] at hlookup_formula
                simpa [ctxAfter, ctx'] using hlookup_res2
              -- We still need a source-regime witness for `res2.regime'`.
              have hkR_res2 : res2.regime'.lookup? k ≠ none := by
                have hkR_inv : (invalidateRegimeDeps res2.regime' res2.tagEnv' ls).lookup? k ≠ none := by
                  simpa [hRegime] using hkR_res
                exact
                  invalidateRegimeDeps_lookup_ne_none_implies_original_ne_none
                    res2.regime' res2.tagEnv' ls k hkR_inv
              have hloc2 := hcwr₁2.1 l qt k hlookup_ctx2 hguard hkR_res2
              cases hloc2 with
              | noPred_ok hnp =>
                  exfalso
                  simp [hnp] at hguard
              | guardOnly_ok k' hgo =>
                  exact locsRegime.guardOnly_ok (l, qt) k' hgo
              | withPred_ok k' arg_name pred_body var_env a n b hclos hreg hreal hmem hcons =>
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
                  have hreg_res2 : res2.regime'.lookup? k = some b := by
                    simpa [ctxAfter, ctx', hk_eq] using hreg
                  have hkeep : (invalidateTagDeps res2.tagEnv' ls).contains k = true :=
                    invalidateRegimeDeps_survives_of_lookup_ne_none res2.regime' res2.tagEnv' ls k
                      (by simpa [hRegime] using hkR_res)
                  have hlookup_eq :
                      (ctxAfter ctxᵢ res).regime.lookup? k = res2.regime'.lookup? k := by
                    simpa [ctxAfter, hRegime] using
                      invalidateRegimeDeps_lookup_eq_lookup_of_surviving_tag res2.regime' res2.tagEnv' ls k hkeep
                  have hregR : (ctxAfter ctxᵢ res).regime.lookup? k' = some b := by
                    calc
                      (ctxAfter ctxᵢ res).regime.lookup? k' = (ctxAfter ctxᵢ res).regime.lookup? k := by simp [hk_eq]
                      _ = res2.regime'.lookup? k := hlookup_eq
                      _ = some b := hreg_res2
                  have hreal' : θ₁2.lookup (l, qt).1 = some a := by
                    simpa using hreal
                  have hvloc₁ : valueHasETyp θ₁1 (Value.loc a₁w) (ETyp.ref ls) := by
                    simpa [hRef] using _hvtyp₁1
                  have hne_a : a ≠ a₁w := by
                    intro haeq
                    cases hvloc₁ with
                    | loc hlookup_w hin_w =>
                        have hlookup_w' : θ₁2.lookup _ = some a₁w := hθext₁2.1 _ _ hlookup_w
                        have hlookup_l : θ₁2.lookup l = some a₁w := by
                          simpa [haeq] using hreal'
                        have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁1wf
                        have hl_eq : l = _ := hθ₁2wf _ _ _ hlookup_l hlookup_w'
                        have : l ∈ ls := by simpa [hl_eq] using hin_w
                        exact hIn this
                  have hcmp : compare a₁w a ≠ Ordering.eq := by
                    intro hce
                    have : a₁w = a := (Nat.compare_eq_eq).1 hce
                    exact hne_a this.symm
                  have hmem' : cf₁.memory.lookup a = some n := by
                    rw [hmem₁]
                    have : cfg₁2.memory.lookup a = some n := hmem
                    simpa [Memory.lookup, Std.ExtTreeMap.getElem?_insert, hcmp] using this
                  have hPredSat_mem :
                      ∀ (k : Tag) (μ μ' : Memory) (v : Value), predSat k μ v ↔ predSat k μ' v := by
                    intro k μ μ' v
                    exact predSat_mem_noPred_compat hpredlaws θ₁2 k μ μ' v
                  have hqtypPredHolds_mem :
                      ∀ (qt : QTyp) (v : Value) (μ μ' : Memory),
                        qtypPredHolds predSat qt μ v ↔ qtypPredHolds predSat qt μ' v := by
                    intro qt v μ μ'
                    constructor
                    · intro hholds
                      cases hholds with
                      | noPred_ok hpred =>
                          exact qtypPredHolds.noPred_ok hpred
                      | guardClosure_ok hpred hSat =>
                          exact qtypPredHolds.guardClosure_ok hpred ((hPredSat_mem _ μ μ' v).1 hSat)
                      | guardOnly_ok hpred hSat =>
                          exact qtypPredHolds.guardOnly_ok hpred ((hPredSat_mem _ μ μ' v).1 hSat)
                    · intro hholds
                      cases hholds with
                      | noPred_ok hpred =>
                          exact qtypPredHolds.noPred_ok hpred
                      | guardClosure_ok hpred hSat =>
                          exact qtypPredHolds.guardClosure_ok hpred ((hPredSat_mem _ μ μ' v).2 hSat)
                      | guardOnly_ok hpred hSat =>
                          exact qtypPredHolds.guardOnly_ok hpred ((hPredSat_mem _ μ μ' v).2 hSat)
                  have hcons' :
                      (b = true → qtypPredHolds predSat qt cf₁.memory (Value.num n)) ∧
                      (b = false → ¬ qtypPredHolds predSat qt cf₁.memory (Value.num n)) := by
                    constructor
                    · intro hbtrue
                      have hholds_old := hcons.1 hbtrue
                      exact (hqtypPredHolds_mem qt (Value.num n) cfg₁2.memory cf₁.memory).1 hholds_old
                    · intro hbfalse hholds_new
                      have hholds_old :=
                        (hqtypPredHolds_mem qt (Value.num n) cfg₁2.memory cf₁.memory).2 hholds_new
                      exact (hcons.2 hbfalse) hholds_old
                  exact locsRegime.withPred_ok (l, qt) k' arg_name pred_body var_env a n b hclos hregR hreal' hmem' hcons'
        | inr _hIn =>
            -- Updated location branch.
            cases hpred : qt.pred with
            | noPred =>
                simp [qtypGuardTag, hpred] at hguard
            | guardOnly k' =>
                exact locsRegime.guardOnly_ok (l, qt) k' hpred
            | guardClosure k' arg_name pred_body var_env =>
                -- Remaining hard subcase: updated location carrying guardClosure predicate.
                exfalso
                have hk_eq : k' = k := by
                  have : some k' = some k := by
                    calc
                      some k' = qtypGuardTag qt := by simp [qtypGuardTag, hpred]
                      _ = some k := hguard
                  exact Option.some.inj this
                have hpred_res2 :
                    res2.qualType.pred = Predicate.guardClosure k' arg_name pred_body var_env := by
                  exact
                    assign_mem_formula_guardClosure_lookup_implies_rhs_pred
                      (ctxᵢ := ctxᵢ) (res1 := res1) (res2 := res2) (res := res)
                      (ls := ls) (l := l) (qt := qt)
                      (k := k') (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
                      hmem_res _hIn hlookup_res hpred
                have hnone : res2.tagEnv'.get? k' = none := by
                  exact
                    guardClosure_pred_implies_tag_absent
                      (ctx := { ctxᵢ with
                        memEnv := res1.memEnv'
                        tagEnv := res1.tagEnv'
                        nextLoc := res1.nextLoc'
                        nextTag := res1.nextTag'
                        regime := res1.regime' })
                      (e := e2) (fuel := fuel') (res := res2)
                      (k := k') (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
                      htc2_expr htagBounded' hpred_res2
                have htagInvalid :
                    ∀ tv, res2.tagEnv'.get? k' = some tv → tv.deps.any ls.contains = true := by
                  intro tv hget'
                  rw [hnone] at hget'
                  cases hget'
                have hnoneInv :
                    (invalidateRegimeDeps res2.regime' res2.tagEnv' ls).lookup? k' = none :=
                  assign_updated_new_guardClosure_implies_invalidated_regime_none
                    res2.regime' res2.tagEnv' ls k' htagInvalid
                have hkR_inv : (invalidateRegimeDeps res2.regime' res2.tagEnv' ls).lookup? k' ≠ none := by
                  have hkR_res_k : res.regime'.lookup? k ≠ none := by
                    simpa [ctxAfter] using hkR
                  have hkR_res_k' : res.regime'.lookup? k' ≠ none := by
                    simpa [hk_eq] using hkR_res_k
                  simpa [hRegime] using hkR_res_k'
                exact hkR_inv hnoneInv
      · constructor
        · intro x qt k hlookup hguard hkR
          have hlookup_ctxi : ctxᵢ.varEnv.lookup x = some qt := by
            simpa [ctxAfter] using hlookup
          have hkR_res : res.regime'.lookup? k ≠ none := by
            simpa [ctxAfter] using hkR
          have hkR_ctxi : ctxᵢ.regime.lookup? k ≠ none := by
            have hkR_res' :
                (invalidateRegimeDeps res2.regime' res2.tagEnv' ls).lookup? k ≠ none := by
              simpa [hRegime] using hkR_res
            have hkR_res2 : res2.regime'.lookup? k ≠ none :=
              invalidateRegimeDeps_lookup_ne_none_implies_original_ne_none
                res2.regime' res2.tagEnv' ls k hkR_res'
            exact hmono12.2 k hkR_res2
          have hvars := hcwr₁.2.1 x qt k hlookup_ctxi hguard hkR_ctxi
          have hPredSat_mem :
              ∀ (k : Tag) (μ μ' : Memory) (v : Value), predSat k μ v ↔ predSat k μ' v := by
            intro k μ μ' v
            exact predSat_mem_noPred_compat hpredlaws θ₁2 k μ μ' v
          have hqtypPredHolds_mem :
              ∀ (qt : QTyp) (v : Value) (μ μ' : Memory),
                qtypPredHolds predSat qt μ v ↔ qtypPredHolds predSat qt μ' v := by
            intro qt v μ μ'
            constructor
            · intro h
              cases h with
              | noPred_ok hpred =>
                  exact qtypPredHolds.noPred_ok hpred
              | guardClosure_ok hpred hSat =>
                  exact qtypPredHolds.guardClosure_ok hpred ((hPredSat_mem _ μ μ' v).1 hSat)
              | guardOnly_ok hpred hSat =>
                  exact qtypPredHolds.guardOnly_ok hpred ((hPredSat_mem _ μ μ' v).1 hSat)
            · intro h
              cases h with
              | noPred_ok hpred =>
                  exact qtypPredHolds.noPred_ok hpred
              | guardClosure_ok hpred hSat =>
                  exact qtypPredHolds.guardClosure_ok hpred ((hPredSat_mem _ μ μ' v).2 hSat)
              | guardOnly_ok hpred hSat =>
                  exact qtypPredHolds.guardOnly_ok hpred ((hPredSat_mem _ μ μ' v).2 hSat)
          have hvar_cf₁ : cf₁.varEnv = ρ₁ := by
            rcases ht₁ with ⟨fuel₁w, verbose₁w, hpure₁w⟩
            have hvar_eq :=
                beval_preserves_varEnv (e1.assign e2) fuel₁w verbose₁w
                { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁
                hpure₁w
            simpa using hvar_eq.symm
          cases hvars with
          | noPred_ok hnp =>
              exact varsRegime.noPred_ok (x, qt) hnp
          | guardOnly_ok k' hgo =>
              exact varsRegime.guardOnly_ok (x, qt) k' hgo
          | withPred_ok k' arg_name pred_body var_env v b hclos hreg hvar hcons =>
              have hk_eq : k' = k := by
                have hclos' : qt.pred = Predicate.guardClosure k' arg_name pred_body var_env := by
                  simpa using hclos
                have hguard' : qtypGuardTag qt = some k' := by
                  simp [qtypGuardTag, hclos']
                have : some k' = some k := by
                  simpa [hguard'] using hguard
                exact Option.some.inj this
              subst k'
              have hkR_res' :
                  (invalidateRegimeDeps res2.regime' res2.tagEnv' ls).lookup? k ≠ none := by
                simpa [hRegime] using hkR_res
              have hkR_res2 : res2.regime'.lookup? k ≠ none :=
                invalidateRegimeDeps_lookup_ne_none_implies_original_ne_none
                  res2.regime' res2.tagEnv' ls k hkR_res'
              have hreg_res2 : res2.regime'.lookup? k = some b := by
                have hmono_keep : res2.regime'.lookup? k = some b ∨ res2.regime'.lookup? k = none :=
                  hmono12.1 k b hreg
                cases hmono_keep with
                | inl hk_keep =>
                    exact hk_keep
                | inr hk_none =>
                    exact (hkR_res2 hk_none).elim
              have hkeep : (invalidateTagDeps res2.tagEnv' ls).contains k = true :=
                invalidateRegimeDeps_survives_of_lookup_ne_none res2.regime' res2.tagEnv' ls k hkR_res'
              have hlookup_eq :
                  (ctxAfter ctxᵢ res).regime.lookup? k = res2.regime'.lookup? k := by
                simpa [ctxAfter, hRegime] using
                  invalidateRegimeDeps_lookup_eq_lookup_of_surviving_tag res2.regime' res2.tagEnv' ls k hkeep
              have hregR : (ctxAfter ctxᵢ res).regime.lookup? k = some b := by
                calc
                  (ctxAfter ctxᵢ res).regime.lookup? k = res2.regime'.lookup? k := hlookup_eq
                  _ = some b := hreg_res2
              have hvar' : cf₁.varEnv.lookup x = some v := by
                simpa [hvar_cf₁] using hvar
              have hcons' :
                  (b = true → qtypPredHolds predSat qt cf₁.memory v) ∧
                  (b = false → ¬ qtypPredHolds predSat qt cf₁.memory v) := by
                constructor
                · intro hbtrue
                  have hholds_old := hcons.1 hbtrue
                  exact (hqtypPredHolds_mem qt v μ₁ cf₁.memory).1 hholds_old
                · intro hbfalse hholds_new
                  have hholds_old := (hqtypPredHolds_mem qt v μ₁ cf₁.memory).2 hholds_new
                  exact (hcons.2 hbfalse) hholds_old
              exact varsRegime.withPred_ok (x, qt) k arg_name pred_body var_env v b hclos hregR hvar' hcons'
        · intro x qt v hlookup hlookup_v
          have hlookup_ctx2 : (ctxAfter ctx' res2).varEnv.lookup x = some qt := by
            simpa [ctxAfter, ctx'] using hlookup
          have hlookup_v_ctx2 : cfg₁2.varEnv.lookup x = some v := by
            simpa [hvar₁] using hlookup_v
          have hcap_ctx2 :
              closureCapturedVarsRegime predSat (ctxAfter ctx' res2).regime qt cfg₁2.memory θ₁2 v :=
            hcwr₁2.2.2 x qt v hlookup_ctx2 hlookup_v_ctx2
          have hmono_res2_to_final :
              Regime.monotoneStep (ctxAfter ctx' res2).regime (ctxAfter ctxᵢ res).regime := by
            simpa [ctxAfter, ctx', hRegime] using
              invalidateRegimeDeps_monotone res2.regime' res2.tagEnv' ls
          have hcap_final_regime :
              closureCapturedVarsRegime predSat (ctxAfter ctxᵢ res).regime qt cfg₁2.memory θ₁2 v :=
            closureCapturedVarsRegime_monotone hmono_res2_to_final hcap_ctx2
          have hpred_compat :
              ∀ (qt' : QTyp) (v' : Value),
                qtypPredHolds predSat qt' cfg₁2.memory v' ↔
                  qtypPredHolds predSat qt' cf₁.memory v' :=
            qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₁2 cfg₁2.memory cf₁.memory
          exact closureCapturedVarsRegime_transport_μ hpred_compat hcap_final_regime
    · have hclean_ctxi :
          ∀ qt, qtypCleanUnder (ctxAfter ctxᵢ res).regime qt → qtypCleanUnder ctxᵢ.regime qt := by
        intro qt hclean
        have hclean_inv :
            qtypCleanUnder (invalidateRegimeDeps res2.regime' res2.tagEnv' ls) qt := by
          simpa [ctxAfter, hRegime] using hclean
        have hclean_res2 : qtypCleanUnder res2.regime' qt :=
          qtypCleanUnder_of_invalidateRegimeDeps res2.regime' res2.tagEnv' ls hclean_inv
        exact qtypCleanUnder_of_monotone hmono12 hclean_res2
      have hmem_split_final :
          ∀ l qt,
            (ctxAfter ctxᵢ res).memEnv.lookup l = some qt →
            res2.memEnv'.contains l = true ∨ l ∈ ls := by
        intro l qt hlookup
        have hlookup_res : res.memEnv'.lookup l = some qt := by
          simpa [ctxAfter] using hlookup
        have hcontains_res : res.memEnv'.contains l = true := by
          have h := memEnv_contains_of_lookup_some res.memEnv' l qt hlookup_res
          exact (Std.ExtTreeMap.contains_iff_mem).2 h
        have hcontains_formula :
            (match Std.ExtTreeSet.toList ls with
              | [l0] =>
                  updateMemEnv res2.memEnv' l0
                    { etyp := ETyp.int
                      poison := joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison)
                      pred := if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred }
              | _ =>
                  updateLocsetWeak res2.memEnv' ls
                    (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                    (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)).contains l = true := by
          simpa [hmem_res] using hcontains_res
        exact
          assign_memEnv_formula_contains_eq_or_mem
            res2.memEnv' ls
            (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
            (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)
            l hcontains_formula
      have hlookup_ctx2_of_not_mem :
          ∀ l qt,
            (ctxAfter ctxᵢ res).memEnv.lookup l = some qt →
            l ∉ ls →
            (ctxAfter ctx' res2).memEnv.lookup l = some qt := by
        intro l qt hlookup hnot
        have hlookup_res : res.memEnv'.lookup l = some qt := by
          simpa [ctxAfter] using hlookup
        have hlookup_formula :
            (match Std.ExtTreeSet.toList ls with
              | [l0] =>
                  updateMemEnv res2.memEnv' l0
                    { etyp := ETyp.int
                      poison := joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison)
                      pred := if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred }
              | _ =>
                  updateLocsetWeak res2.memEnv' ls
                    (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                    (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)).lookup l = some qt := by
          simpa [hmem_res] using hlookup_res
        have hlookup_res2 : res2.memEnv'.lookup l = some qt := by
          have hlookup_eq :
              (match Std.ExtTreeSet.toList ls with
                | [l0] =>
                    updateMemEnv res2.memEnv' l0
                      { etyp := ETyp.int
                        poison := joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison)
                        pred := if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred }
                | _ =>
                    updateLocsetWeak res2.memEnv' ls
                      (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                      (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)).lookup l =
                  res2.memEnv'.lookup l :=
            assign_memEnv_formula_lookup_eq_of_not_mem
              res2.memEnv' ls
              (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
              (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)
              l hnot
          rwa [hlookup_eq] at hlookup_formula
        simpa [ctxAfter, ctx'] using hlookup_res2
      have htag_entry_of_final_regime_lookup :
          ∀ k, (ctxAfter ctxᵢ res).regime.lookup? k ≠ none →
            ∃ tv, res2.tagEnv'.get? k = some tv ∧ tv.deps.any ls.contains = false := by
        intro k hkR
        have hkR_inv : (invalidateRegimeDeps res2.regime' res2.tagEnv' ls).lookup? k ≠ none := by
          simpa [ctxAfter, hRegime] using hkR
        exact
          invalidateRegimeDeps_lookup_ne_none_implies_surviving_tag_entry
            res2.regime' res2.tagEnv' ls k hkR_inv
      have hres2_regime_or_false_tag_of_final_lookup :
          ∀ k, (ctxAfter ctxᵢ res).regime.lookup? k ≠ none →
            res2.regime'.lookup? k ≠ none ∨
              ∃ deps, res2.tagEnv'.get? k = some ⟨false, deps⟩ := by
        intro k hkR
        have htag_res2 : tagEnvConsistentWithRegime res2.tagEnv' res2.regime' := by
          simpa [ctxAfter, ctx'] using hregCtx2
        have hkR_inv : (invalidateRegimeDeps res2.regime' res2.tagEnv' ls).lookup? k ≠ none := by
          simpa [ctxAfter, hRegime] using hkR
        exact
          regime_lookup_ne_none_or_false_tag_of_invalidate_lookup
            res2.regime' res2.regime' res2.tagEnv' ls k htag_res2 hkR_inv
      refine agreeOnClean_transport_assign_final_of_split
        (predSat := predSat)
        (ctxFinal := (ctxAfter ctxᵢ res))
        (cf₀ := cf₀) (cf₁ := cf₁) (θ₀2 := θ₀2) (θ₁2 := θ₁2)
        ?_ ?_
      · intro l qt hlookup hclean
        have hmono_res2_to_final :
            Regime.monotoneStep (ctxAfter ctx' res2).regime (ctxAfter ctxᵢ res).regime := by
          simpa [ctxAfter, hRegime] using
            invalidateRegimeDeps_monotone res2.regime' res2.tagEnv' ls
        have hclean_res2 : qtypCleanUnder (ctxAfter ctx' res2).regime qt := by
          exact
            qtypCleanUnder_of_invalidateRegimeDeps
              res2.regime' res2.tagEnv' ls (by simpa [ctxAfter, hRegime] using hclean)
        by_cases hIn : l ∈ ls
        · by_cases hcontains : res2.memEnv'.contains l = true
          · have hlookup_res : res.memEnv'.lookup l = some qt := by
              simpa [ctxAfter] using hlookup
            have hlookup_formula :
                (match Std.ExtTreeSet.toList ls with
                  | [l0] =>
                      updateMemEnv res2.memEnv' l0
                        { etyp := ETyp.int
                          poison := joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison)
                          pred := if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred }
                  | _ =>
                      updateLocsetWeak res2.memEnv' ls
                        (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                        (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)).lookup l = some qt := by
              simpa [hmem_res] using hlookup_res
            cases hls : Std.ExtTreeSet.toList ls with
            | nil =>
                have hInList : l ∈ ls.toList := (Std.ExtTreeSet.mem_toList).2 hIn
                simp [hls] at hInList
            | cons x xs =>
                cases xs with
                | nil =>
                    have hlEq : x = l := by
                      have hInList : l ∈ ls.toList := (Std.ExtTreeSet.mem_toList).2 hIn
                      have hlEq' : l = x := by
                        simpa [hls] using hInList
                      exact hlEq'.symm
                    subst x
                    have hlookup_single :
                        (updateMemEnv res2.memEnv' l
                          { etyp := ETyp.int
                            poison := joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison)
                            pred := if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred }).lookup l =
                          some qt := by
                      simpa [hls] using hlookup_formula
                    have hqtEq :
                        qt =
                          { etyp := ETyp.int
                            poison := joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison)
                            pred := if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred } := by
                      simpa [updateMemEnv, MemoryTypeEnv.lookup] using hlookup_single.symm
                    have hvloc₀ : valueHasETyp θ₀1 (Value.loc a₀w) (ETyp.ref ls) := by
                      simpa [hRef] using _hvtyp₀1
                    have hvloc₁ : valueHasETyp θ₁1 (Value.loc a₁w) (ETyp.ref ls) := by
                      simpa [hRef] using _hvtyp₁1
                    have hreal₀ : θ₀2.lookup l = some a₀w := by
                      cases hvloc₀ with
                      | @loc _ _ lw hlookup_w hin_w =>
                          have hlwEq : lw = l := by
                            have hlwInList : lw ∈ ls.toList := (Std.ExtTreeSet.mem_toList).2 hin_w
                            simpa [hls] using hlwInList
                          subst hlwEq
                          exact hθext₀2.1 _ _ hlookup_w
                    have hreal₁ : θ₁2.lookup l = some a₁w := by
                      cases hvloc₁ with
                      | @loc _ _ lw hlookup_w hin_w =>
                          have hlwEq : lw = l := by
                            have hlwInList : lw ∈ ls.toList := (Std.ExtTreeSet.mem_toList).2 hin_w
                            simpa [hls] using hlwInList
                          subst hlwEq
                          exact hθext₁2.1 _ _ hlookup_w
                    have hlookup₀_final : cf₀.memory.lookup a₀w = some n₀ := by
                      rw [hmem₀]
                      simp [Memory.lookup]
                    have hlookup₁_final : cf₁.memory.lookup a₁w = some n₁ := by
                      rw [hmem₁]
                      simp [Memory.lookup]
                    have hclean_rhs : qtypCleanUnder (ctxAfter ctx' res2).regime res2.qualType := by
                      cases hclean_res2 with
                      | clean hpoison =>
                          have hjoin : joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison) = false := by
                            simpa [hqtEq] using hpoison
                          have hsplit : ctxᵢ.pc = false ∧ res1.qualType.poison = false ∧ res2.qualType.poison = false := by
                            simpa [joinPoison] using hjoin
                          exact qtypCleanUnder.clean hsplit.2.2
                      | guard k htag hreg hnotfun =>
                          have htag_rhs : qtypGuardTag res2.qualType = some k := by
                            have htag_stored :
                                qtypGuardTag
                                  { etyp := ETyp.int
                                    poison := joinPoison ctxᵢ.pc
                                      (joinPoison res1.qualType.poison res2.qualType.poison)
                                    pred := if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred } =
                                  some k := by
                              simpa [hqtEq] using htag
                            by_cases hwrite : res1.qualType.poison = true ∨ ctxᵢ.pc = true
                            · simp [qtypGuardTag, hwrite] at htag_stored
                            · simpa [qtypGuardTag, hwrite] using htag_stored
                          have hnotfun_rhs : res2.qualType.etyp.isFunctionType = false := by
                            simp [hInt, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                          exact qtypCleanUnder.guard k htag_rhs hreg hnotfun_rhs
                    have hagree_rhs :
                        agreeValueUnder predSat (ctxAfter ctx' res2).regime
                          cfg₀2.memory cfg₁2.memory θ₀2 θ₁2
                          res2.qualType (Value.num n₀) (Value.num n₁) :=
                      hres_agree2 hclean_rhs
                    have hetyp_qt_rhs : qt.etyp = res2.qualType.etyp := by
                      calc
                        qt.etyp = ETyp.int := by simp [hqtEq]
                        _ = res2.qualType.etyp := hInt.symm
                    have hpoison_imp : qt.poison = false → res2.qualType.poison = false := by
                      intro hpoison_qt
                      have hjoin : joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison) = false := by
                        simpa [hqtEq] using hpoison_qt
                      have hsplit : ctxᵢ.pc = false ∧ res1.qualType.poison = false ∧ res2.qualType.poison = false := by
                        simpa [joinPoison] using hjoin
                      exact hsplit.2.2
                    have hagree_qt_res2 :
                        agreeValueUnder predSat (ctxAfter ctx' res2).regime
                          cfg₀2.memory cfg₁2.memory θ₀2 θ₁2
                          qt (Value.num n₀) (Value.num n₁) :=
                      agreeValueUnder_transport_clean
                        (predSat := predSat)
                        (R := (ctxAfter ctx' res2).regime)
                        (μ₀ := cfg₀2.memory) (μ₁ := cfg₁2.memory)
                        (θ₀ := θ₀2) (θ₁ := θ₁2)
                        (qt := qt) (qt2 := res2.qualType)
                        (o₀ := Value.num n₀) (o₁ := Value.num n₁)
                        hclean_res2 hetyp_qt_rhs hpoison_imp hagree_rhs
                    have hagree_qt_final :
                        agreeValueUnder predSat (ctxAfter ctxᵢ res).regime
                          cf₀.memory cf₁.memory θ₀2 θ₁2
                          qt (Value.num n₀) (Value.num n₁) := by
                      have htmp :
                          agreeValueUnder predSat (ctxAfter ctxᵢ res).regime
                            (Std.ExtTreeMap.insert cfg₀2.memory a₀w n₀)
                            (Std.ExtTreeMap.insert cfg₁2.memory a₁w n₁)
                            θ₀2 θ₁2 qt (Value.num n₀) (Value.num n₁) := by
                        exact
                          agreeValueUnder_transport_insert_clean_monotone
                            (R := (ctxAfter ctx' res2).regime) (R' := (ctxAfter ctxᵢ res).regime)
                            (μ₀ := cfg₀2.memory) (μ₁ := cfg₁2.memory)
                            (θ₀ := θ₀2) (θ₁ := θ₁2) (qt := qt)
                            (v₀ := Value.num n₀) (v₁ := Value.num n₁)
                            a₀w a₁w n₀ n₁
                            (hpred_compat₀ := fun qt' v' =>
                              qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₀2 cfg₀2.memory (Std.ExtTreeMap.insert cfg₀2.memory a₀w n₀) qt' v')
                            (hpred_compat₁ := fun qt' v' =>
                              qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₁2 cfg₁2.memory (Std.ExtTreeMap.insert cfg₁2.memory a₁w n₁) qt' v')
                            hmono_res2_to_final hclean hagree_qt_res2
                      simpa [hmem₀, hmem₁] using htmp
                    exact
                      agreeLocUnder.agree_values l qt a₀w a₁w n₀ n₁
                        hreal₀ hreal₁ hlookup₀_final hlookup₁_final
                        hagree_qt_final
                | cons y ys =>
                    cases hclean with
                    | clean hpoison =>
                        have hcontains_getElem : (res2.memEnv'[l]?).isSome = true := by
                          have hcontains' := hcontains
                          rw [Std.ExtTreeMap.contains_eq_isSome_getElem?] at hcontains'
                          exact hcontains'
                        cases hget : res2.memEnv'[l]? with
                        | none =>
                            simp [hget] at hcontains_getElem
                        | some e_old =>
                            let qtOld : QTyp := ⟨ETyp.int, e_old.poison, e_old.pred⟩
                            have hlookup_old : res2.memEnv'.lookup l = some qtOld := by
                              simp only [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?, hget, Option.map]; rfl
                            have hlookup_old' : (ctxAfter ctx' res2).memEnv.lookup l = some qtOld := by
                              simpa [ctxAfter, ctx'] using hlookup_old
                            have hclean_old : qtypCleanUnder (ctxAfter ctx' res2).regime qtOld := by
                              have hlookup_weak :
                                  (updateLocsetWeak res2.memEnv' ls
                                    (joinPoison ctxᵢ.pc
                                      (joinPoison res1.qualType.poison res2.qualType.poison))
                                    (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)).lookup l =
                                    some qt := by
                                simpa [hls] using hlookup_formula
                              unfold updateLocsetWeak at hlookup_weak
                              set joined :=
                                LocSet.fold ls
                                  (joinPoison ctxᵢ.pc
                                    (joinPoison res1.qualType.poison res2.qualType.poison),
                                    if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)
                                  (fun (accP, accPred) l0 =>
                                    match res2.memEnv'[l0]? with
                                    | some qt0 => (joinPoison accP qt0.poison, joinPredicates accPred qt0.pred)
                                    | none => (accP, accPred)) with hjoined
                              set finalQt : QTyp := ⟨ETyp.int, joined.1, joined.2⟩ with hfinalQt
                              dsimp at hlookup_weak
                              unfold LocSet.fold at hlookup_weak
                              rw [Std.ExtTreeSet.foldl_eq_foldl_toList] at hlookup_weak
                              have hInList : l ∈ ls.toList := (Std.ExtTreeSet.mem_toList).2 hIn
                              have hlookup_final :
                                  (ls.toList.foldl (fun acc l0 => updateMemEnv acc l0 finalQt) res2.memEnv').lookup l =
                                    some finalQt :=
                                list_fold_updateMemEnv_lookup_eq_of_mem ls.toList res2.memEnv' l finalQt hInList rfl
                              have hqtEq : qt = finalQt := by
                                have : some qt = some finalQt := by
                                  calc
                                    some qt =
                                        (ls.toList.foldl (fun acc l0 => updateMemEnv acc l0 finalQt) res2.memEnv').lookup l := by
                                          symm
                                          exact hlookup_weak
                                    _ = some finalQt := hlookup_final
                                exact Option.some.inj this
                              have hjoined_false : joined.1 = false := by
                                simpa [hqtEq, hfinalQt] using hpoison
                              have hjoined_fold :
                                  ((ls.toList.foldl
                                      (fun acc l0 =>
                                        match res2.memEnv'[l0]? with
                                        | some qt0 => (joinPoison acc.1 qt0.poison, joinPredicates acc.2 qt0.pred)
                                        | none => acc)
                                      (joinPoison ctxᵢ.pc
                                          (joinPoison res1.qualType.poison res2.qualType.poison),
                                        if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)).1) =
                                    false := by
                                unfold joined at hjoined_false
                                unfold LocSet.fold at hjoined_false
                                rw [Std.ExtTreeSet.foldl_eq_foldl_toList] at hjoined_false
                                exact hjoined_false
                              have hpoison_old : qtOld.poison = false :=
                                list_fold_joinPoison_false_implies_lookup_poison_false
                                  res2.memEnv' ls.toList
                                  (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                                  (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)
                                  l qtOld hInList hlookup_old hjoined_fold
                              exact qtypCleanUnder.clean hpoison_old
                            have hagree_old := hagree2.1 l qtOld hlookup_old' hclean_old
                            cases hagree_old with
                            | both_unrealized _ _ hnone₀ hnone₁ =>
                                exact agreeLocUnder.both_unrealized l qt hnone₀ hnone₁
                            | agree_values _ _ a0 a1 n₀' n₁' hreal₀ hreal₁ hlookup₀ hlookup₁ hagree_val =>
                                have hlookup_weak :
                                    (updateLocsetWeak res2.memEnv' ls
                                      (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                                      (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)).lookup l =
                                      some qt := by
                                  simpa [hls] using hlookup_formula
                                unfold updateLocsetWeak at hlookup_weak
                                set joined :=
                                  LocSet.fold ls
                                    (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison),
                                      if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)
                                    (fun (accP, accPred) l0 =>
                                      match res2.memEnv'[l0]? with
                                      | some qt0 => (joinPoison accP qt0.poison, joinPredicates accPred qt0.pred)
                                      | none => (accP, accPred)) with hjoined
                                set finalQt : QTyp := ⟨ETyp.int, joined.1, joined.2⟩ with hfinalQt
                                dsimp at hlookup_weak
                                unfold LocSet.fold at hlookup_weak
                                rw [Std.ExtTreeSet.foldl_eq_foldl_toList] at hlookup_weak
                                have hInList : l ∈ ls.toList := (Std.ExtTreeSet.mem_toList).2 hIn
                                have hlookup_final :
                                    (ls.toList.foldl (fun acc l0 => updateMemEnv acc l0 finalQt) res2.memEnv').lookup l =
                                      some finalQt :=
                                  list_fold_updateMemEnv_lookup_eq_of_mem ls.toList res2.memEnv' l finalQt hInList rfl
                                have hqtEq : qt = finalQt := by
                                  have : some qt = some finalQt := by
                                    calc
                                      some qt =
                                          (ls.toList.foldl (fun acc l0 => updateMemEnv acc l0 finalQt) res2.memEnv').lookup l := by
                                            symm
                                            exact hlookup_weak
                                      _ = some finalQt := hlookup_final
                                  exact Option.some.inj this
                                have hetyp_qt : qt.etyp = ETyp.int := by
                                  simp [hqtEq, hfinalQt]
                                have hnotfun_qt : qt.etyp.isFunctionType = false := by
                                  simp [hetyp_qt, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                                have hnotref_qt : ¬ ∃ ls', qt.etyp = ETyp.ref ls' := by
                                  intro href
                                  rcases href with ⟨ls', ht⟩
                                  have : ETyp.int = ETyp.ref ls' := by
                                    simpa [hetyp_qt] using ht.symm
                                  cases this
                                have hEq_old : n₀' = n₁' := by
                                  cases hagree_val with
                                  | clean_eq_nonref_nonarrow _ _ _ hEq =>
                                      simpa [Value.num.injEq] using hEq
                                  | withPred_true_eq _ _ _ _ _ hEq =>
                                      simpa [Value.num.injEq] using hEq
                                  | clean_internal_arrow _ _ _ _ _ _ _ _ _ hv₀ _ =>
                                      cases hv₀
                                  | dirty_internal_arrow _ hisArrow htyp₀ _ =>
                                      have htyp₀_int : qtOld.etyp = ETyp.int :=
                                        valueHasETyp_num_etyp htyp₀
                                      simp [htyp₀_int, ETyp.isArrow] at hisArrow
                                  | clean_internal_parrow _ _ _ _ _ _ _ _ _ hv₀ _ =>
                                      cases hv₀
                                  | dirty_internal_parrow _ hisParrow htyp₀ _ =>
                                      have htyp₀_int : qtOld.etyp = ETyp.int :=
                                        valueHasETyp_num_etyp htyp₀
                                      simp [htyp₀_int, ETyp.isParrow] at hisParrow
                                  | clean_ref _ _ _ _ hv₀ _ _ =>
                                      cases hv₀
                                  | withPred_true_ref _ _ _ _ _ _ hv₀ _ _ =>
                                      cases hv₀
                                have hagree_qt_old :
                                    agreeValueUnder predSat (ctxAfter ctx' res2).regime
                                      cfg₀2.memory cfg₁2.memory θ₀2 θ₁2
                                      qt (Value.num n₀') (Value.num n₁') := by
                                  refine agreeValueUnder.clean_eq_nonref_nonarrow (predSat := predSat)
                                    (R := (ctxAfter ctx' res2).regime)
                                    (qt := qt) (v₁ := Value.num n₀') (v₂ := Value.num n₁')
                                    hpoison hnotfun_qt hnotref_qt ?_
                                  simp [hEq_old]
                                have hjoined_false : joined.1 = false := by
                                  simpa [hqtEq, hfinalQt] using hpoison
                                have hjoined_fold :
                                    ((ls.toList.foldl
                                        (fun acc l0 =>
                                          match res2.memEnv'[l0]? with
                                          | some qt0 => (joinPoison acc.1 qt0.poison, joinPredicates acc.2 qt0.pred)
                                          | none => acc)
                                        (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison),
                                          if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)).1) = false := by
                                  unfold joined at hjoined_false
                                  unfold LocSet.fold at hjoined_false
                                  rw [Std.ExtTreeSet.foldl_eq_foldl_toList] at hjoined_false
                                  exact hjoined_false
                                have hbase_false : joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison) = false := by
                                  cases hbase : joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison) with
                                  | false =>
                                      rfl
                                  | true =>
                                      have hfold_true :
                                          ((ls.toList.foldl
                                              (fun acc l0 =>
                                                match res2.memEnv'[l0]? with
                                                | some qt0 => (joinPoison acc.1 qt0.poison, joinPredicates acc.2 qt0.pred)
                                                | none => acc)
                                              (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison),
                                                if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)).1) = true := by
                                        simpa [hbase] using
                                          list_fold_joinPoison_first_true
                                            res2.memEnv' ls.toList
                                            (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)
                                      have : false = true := hjoined_fold.symm.trans hfold_true
                                      cases this
                                have hbase_split :
                                    ctxᵢ.pc = false ∧ res1.qualType.poison = false ∧ res2.qualType.poison = false := by
                                  simpa [joinPoison] using hbase_false
                                have hres1_clean : qtypCleanUnder (ctxAfter ctxᵢ res1).regime res1.qualType :=
                                  qtypCleanUnder.clean hbase_split.2.1
                                have hres2_clean : qtypCleanUnder (ctxAfter ctx' res2).regime res2.qualType :=
                                  qtypCleanUnder.clean hbase_split.2.2
                                rcases
                                  resultAgreesIfClean_ref_shared_witness
                                    (predSat := predSat)
                                    (R := (ctxAfter ctxᵢ res1).regime)
                                    (μ₀ := cfg₀1.memory) (μ₁ := cfg₁1.memory)
                                    (θ₀ := θ₀1) (θ₁ := θ₁1)
                                    (qt := res1.qualType) (ls := ls)
                                    (a₀w := a₀w) (a₁w := a₁w)
                                    hRef hres_agree1 hres1_clean
                                  with ⟨lw, hlwIn, hwrite₀1, hwrite₁1⟩
                                have hwrite₀ : θ₀2.lookup lw = some a₀w := hθext₀2.1 _ _ hwrite₀1
                                have hwrite₁ : θ₁2.lookup lw = some a₁w := hθext₁2.1 _ _ hwrite₁1
                                by_cases hWrite : l = lw
                                · have ha0 : a0 = a₀w := by
                                    have : some a0 = some a₀w := by
                                      calc
                                        some a0 = θ₀2.lookup l := by symm; exact hreal₀
                                        _ = some a₀w := by simpa [hWrite] using hwrite₀
                                    exact Option.some.inj this
                                  have ha1 : a1 = a₁w := by
                                    have : some a1 = some a₁w := by
                                      calc
                                        some a1 = θ₁2.lookup l := by symm; exact hreal₁
                                        _ = some a₁w := by simpa [hWrite] using hwrite₁
                                    exact Option.some.inj this
                                  have hlookup₀_final : cf₀.memory.lookup a0 = some n₀ := by
                                    rw [hmem₀, ha0]
                                    simp [Memory.lookup]
                                  have hlookup₁_final : cf₁.memory.lookup a1 = some n₁ := by
                                    rw [hmem₁, ha1]
                                    simp [Memory.lookup]
                                  have hetyp_qt_rhs : qt.etyp = res2.qualType.etyp := by
                                    calc
                                      qt.etyp = ETyp.int := hetyp_qt
                                      _ = res2.qualType.etyp := hInt.symm
                                  have hpoison_imp_rhs : qt.poison = false → res2.qualType.poison = false := by
                                    intro _
                                    exact hbase_split.2.2
                                  have hagree_qt_rhs :
                                      agreeValueUnder predSat (ctxAfter ctx' res2).regime
                                        cfg₀2.memory cfg₁2.memory θ₀2 θ₁2
                                        qt (Value.num n₀) (Value.num n₁) :=
                                    agreeValueUnder_transport_clean
                                      (predSat := predSat)
                                      (R := (ctxAfter ctx' res2).regime)
                                      (μ₀ := cfg₀2.memory) (μ₁ := cfg₁2.memory)
                                      (θ₀ := θ₀2) (θ₁ := θ₁2)
                                      (qt := qt) (qt2 := res2.qualType)
                                      (o₀ := Value.num n₀) (o₁ := Value.num n₁)
                                      hclean_res2 hetyp_qt_rhs hpoison_imp_rhs
                                      (hres_agree2 hres2_clean)
                                  have hagree_qt_final :
                                      agreeValueUnder predSat (ctxAfter ctxᵢ res).regime
                                        cf₀.memory cf₁.memory θ₀2 θ₁2
                                        qt (Value.num n₀) (Value.num n₁) := by
                                    have htmp :
                                        agreeValueUnder predSat (ctxAfter ctxᵢ res).regime
                                          (Std.ExtTreeMap.insert cfg₀2.memory a₀w n₀)
                                          (Std.ExtTreeMap.insert cfg₁2.memory a₁w n₁)
                                          θ₀2 θ₁2 qt (Value.num n₀) (Value.num n₁) := by
                                      exact
                                        agreeValueUnder_transport_insert_clean_monotone
                                          (R := (ctxAfter ctx' res2).regime) (R' := (ctxAfter ctxᵢ res).regime)
                                          (μ₀ := cfg₀2.memory) (μ₁ := cfg₁2.memory)
                                          (θ₀ := θ₀2) (θ₁ := θ₁2)
                                          (qt := qt)
                                          (v₀ := Value.num n₀) (v₁ := Value.num n₁)
                                          a₀w a₁w n₀ n₁
                                          (hpred_compat₀ := fun qt' v' =>
                                            qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₀2 cfg₀2.memory (Std.ExtTreeMap.insert cfg₀2.memory a₀w n₀) qt' v')
                                          (hpred_compat₁ := fun qt' v' =>
                                            qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₁2 cfg₁2.memory (Std.ExtTreeMap.insert cfg₁2.memory a₁w n₁) qt' v')
                                          hmono_res2_to_final (qtypCleanUnder.clean hpoison) hagree_qt_rhs
                                    simpa [hmem₀, hmem₁] using htmp
                                  exact
                                    agreeLocUnder.agree_values l qt a0 a1 n₀ n₁
                                      hreal₀ hreal₁ hlookup₀_final hlookup₁_final
                                      hagree_qt_final
                                · have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀1wf
                                  have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁1wf
                                  have ha0_ne : a0 ≠ a₀w := by
                                    intro ha0
                                    apply hWrite
                                    have hlookup_lw : θ₀2.lookup lw = some a0 := by
                                      simpa [ha0] using hwrite₀
                                    exact hθ₀2wf _ _ _ hreal₀ hlookup_lw
                                  have ha1_ne : a1 ≠ a₁w := by
                                    intro ha1
                                    apply hWrite
                                    have hlookup_lw : θ₁2.lookup lw = some a1 := by
                                      simpa [ha1] using hwrite₁
                                    exact hθ₁2wf _ _ _ hreal₁ hlookup_lw
                                  have hlookup₀_final : cf₀.memory.lookup a0 = some n₀' := by
                                    rw [hmem₀]
                                    have hcmp : compare a₀w a0 ≠ Ordering.eq := by
                                      intro hce
                                      have : a₀w = a0 := (Nat.compare_eq_eq).1 hce
                                      exact ha0_ne this.symm
                                    simpa [Memory.lookup, Std.ExtTreeMap.getElem?_insert, hcmp] using hlookup₀
                                  have hlookup₁_final : cf₁.memory.lookup a1 = some n₁' := by
                                    rw [hmem₁]
                                    have hcmp : compare a₁w a1 ≠ Ordering.eq := by
                                      intro hce
                                      have : a₁w = a1 := (Nat.compare_eq_eq).1 hce
                                      exact ha1_ne this.symm
                                    simpa [Memory.lookup, Std.ExtTreeMap.getElem?_insert, hcmp] using hlookup₁
                                  have hagree_qt_final :
                                      agreeValueUnder predSat (ctxAfter ctxᵢ res).regime
                                        cf₀.memory cf₁.memory θ₀2 θ₁2
                                        qt (Value.num n₀') (Value.num n₁') := by
                                    have htmp :
                                        agreeValueUnder predSat (ctxAfter ctxᵢ res).regime
                                          (Std.ExtTreeMap.insert cfg₀2.memory a₀w n₀)
                                          (Std.ExtTreeMap.insert cfg₁2.memory a₁w n₁)
                                          θ₀2 θ₁2 qt (Value.num n₀') (Value.num n₁') := by
                                      exact
                                        agreeValueUnder_transport_insert_clean_monotone
                                          (R := (ctxAfter ctx' res2).regime) (R' := (ctxAfter ctxᵢ res).regime)
                                          (μ₀ := cfg₀2.memory) (μ₁ := cfg₁2.memory)
                                          (θ₀ := θ₀2) (θ₁ := θ₁2)
                                          (qt := qt)
                                          (v₀ := Value.num n₀') (v₁ := Value.num n₁')
                                          a₀w a₁w n₀ n₁
                                          (hpred_compat₀ := fun qt' v' =>
                                            qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₀2 cfg₀2.memory (Std.ExtTreeMap.insert cfg₀2.memory a₀w n₀) qt' v')
                                          (hpred_compat₁ := fun qt' v' =>
                                            qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₁2 cfg₁2.memory (Std.ExtTreeMap.insert cfg₁2.memory a₁w n₁) qt' v')
                                          hmono_res2_to_final (qtypCleanUnder.clean hpoison) hagree_qt_old
                                    simpa [hmem₀, hmem₁] using htmp
                                  exact
                                    agreeLocUnder.agree_values l qt a0 a1 n₀' n₁'
                                      hreal₀ hreal₁ hlookup₀_final hlookup₁_final
                                      hagree_qt_final
                    | guard k htag hreg hnotfun =>
                        cases hpred : qt.pred with
                        | noPred =>
                            simp [qtypGuardTag, hpred] at htag
                        | guardClosure k' arg_name pred_body var_env =>
                            exfalso
                            have hk : k' = k := by
                              have : some k' = some k := by
                                simpa [qtypGuardTag, hpred] using htag
                              exact Option.some.inj this
                            have hpred_res2 :
                                res2.qualType.pred = Predicate.guardClosure k' arg_name pred_body var_env := by
                              exact
                                assign_mem_formula_guardClosure_lookup_implies_rhs_pred
                                  (ctxᵢ := ctxᵢ) (res1 := res1) (res2 := res2) (res := res)
                                  (ls := ls) (l := l) (qt := qt)
                                  (k := k') (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
                                  hmem_res hIn hlookup_res hpred
                            have hnone : res2.tagEnv'.get? k' = none := by
                              exact
                                guardClosure_pred_implies_tag_absent
                                  (ctx := { ctxᵢ with
                                    memEnv := res1.memEnv'
                                    tagEnv := res1.tagEnv'
                                    nextLoc := res1.nextLoc'
                                    nextTag := res1.nextTag'
                                    regime := res1.regime' })
                                  (e := e2) (fuel := fuel') (res := res2)
                                  (k := k') (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
                                  htc2_expr htagBounded' hpred_res2
                            have hkLive : (ctxAfter ctxᵢ res).regime.lookup? k' ≠ none := by
                              simp [hk, hreg]
                            rcases htag_entry_of_final_regime_lookup k' hkLive with ⟨tv, hgettv, _⟩
                            rw [hnone] at hgettv
                            cases hgettv
                        | guardOnly k' =>
                            have hk : k' = k := by
                              have : some k' = some k := by
                                simpa [qtypGuardTag, hpred] using htag
                              exact Option.some.inj this
                            subst hk
                            have hcontains_getElem : (res2.memEnv'[l]?).isSome = true := by
                              have hcontains' := hcontains
                              rw [Std.ExtTreeMap.contains_eq_isSome_getElem?] at hcontains'
                              exact hcontains'
                            cases hget : res2.memEnv'[l]? with
                            | none =>
                                simp [hget] at hcontains_getElem
                            | some qtOld =>
                                set qtOldQ : QTyp := ⟨ETyp.int, qtOld.poison, qtOld.pred⟩ with hqtOldQ
                                have hlookup_old : res2.memEnv'.lookup l = some qtOldQ := by
                                  simp only [MemoryTypeEnv.lookup, hqtOldQ, Std.ExtTreeMap.get?_eq_getElem?, hget, Option.map]
                                have hlookup_old' : (ctxAfter ctx' res2).memEnv.lookup l = some qtOldQ := by
                                  simpa [ctxAfter, ctx'] using hlookup_old
                                have hlookup_weak :
                                    (updateLocsetWeak res2.memEnv' ls
                                      (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                                      (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)).lookup
                                    l = some qt := by
                                  simpa [hls] using hlookup_formula
                                unfold updateLocsetWeak at hlookup_weak
                                set joined :=
                                  LocSet.fold ls
                                    (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison),
                                      if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)
                                    (fun (accP, accPred) l0 =>
                                      match res2.memEnv'.get? l0 with
                                      | some qt0 => (joinPoison accP qt0.poison, joinPredicates accPred qt0.pred)
                                      | none => (accP, accPred)) with hjoined
                                set finalQt : QTyp := ⟨ETyp.int, joined.1, joined.2⟩ with hfinalQt
                                dsimp at hlookup_weak
                                unfold LocSet.fold at hlookup_weak
                                rw [Std.ExtTreeSet.foldl_eq_foldl_toList] at hlookup_weak
                                have hInList : l ∈ ls.toList := (Std.ExtTreeSet.mem_toList).2 hIn
                                have hlookup_final :
                                    (ls.toList.foldl (fun acc l0 => updateMemEnv acc l0 finalQt) res2.memEnv').lookup l =
                                      some finalQt :=
                                  list_fold_updateMemEnv_lookup_eq_of_mem ls.toList res2.memEnv' l finalQt hInList rfl
                                have hqtEq : qt = finalQt := by
                                  have : some qt = some finalQt := by
                                    calc
                                      some qt =
                                          (ls.toList.foldl (fun acc l0 => updateMemEnv acc l0 finalQt) res2.memEnv').lookup l := by
                                            symm
                                            exact hlookup_weak
                                      _ = some finalQt := hlookup_final
                                  exact Option.some.inj this
                                have hetyp_qt : qt.etyp = ETyp.int := by
                                  simp [hqtEq, hfinalQt]
                                have hnotref_qt : ¬ ∃ ls', qt.etyp = ETyp.ref ls' := by
                                  intro href
                                  rcases href with ⟨ls', ht⟩
                                  have : ETyp.int = ETyp.ref ls' := by
                                    simpa [hetyp_qt] using ht.symm
                                  cases this
                                have hjoined_pred : joined.2 = Predicate.guardOnly k' := by
                                  have : finalQt.pred = Predicate.guardOnly k' := by
                                    simpa [hqtEq] using hpred
                                  simpa [hfinalQt] using this
                                have hfold_pred :
                                    ((ls.toList.foldl
                                        (fun acc l0 =>
                                          match res2.memEnv'[l0]? with
                                          | some qt0 => (joinPoison acc.1 qt0.poison, joinPredicates acc.2 qt0.pred)
                                          | none => acc)
                                        (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison),
                                          if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)).2) =
                                      Predicate.guardOnly k' := by
                                  unfold joined at hjoined_pred
                                  unfold LocSet.fold at hjoined_pred
                                  rw [Std.ExtTreeSet.foldl_eq_foldl_toList] at hjoined_pred
                                  exact hjoined_pred
                                have htag_init_and_all :=
                                  list_fold_joinPredicates_guardOnly_implies_init_and_lookup_guardTag
                                    res2.memEnv' ls.toList
                                    (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                                    (if res1.qualType.poison = true ∨ ctxᵢ.pc = true then Predicate.noPred else res2.qualType.pred)
                                    (k := k') hfold_pred
                                rcases htag_init_and_all with ⟨htag_stored, htag_each⟩
                                have hres1_poison : res1.qualType.poison = false := by
                                  cases hp : res1.qualType.poison with
                                  | false => rfl
                                  | true =>
                                      exfalso
                                      simp [hp, qtypGuardTag] at htag_stored
                                have htag_rhs : qtypGuardTag res2.qualType = some k' := by
                                  have htag' :
                                      qtypGuardTag { etyp := ETyp.int, poison := false, pred := res2.qualType.pred } =
                                        some k' := by
                                    by_cases hpc : ctxᵢ.pc = true
                                    · simp [hres1_poison, hpc, qtypGuardTag] at htag_stored
                                    · simpa [hres1_poison, hpc] using htag_stored
                                  simpa [qtypGuardTag] using htag'
                                have htag_old : qtypGuardTag qtOldQ = some k' :=
                                  htag_each l qtOldQ hInList hlookup_old
                                have hkeep : (invalidateTagDeps res2.tagEnv' ls).contains k' = true :=
                                  invalidateRegimeDeps_survives_of_lookup_ne_none
                                    res2.regime' res2.tagEnv' ls k' (by
                                      have :
                                          (invalidateRegimeDeps res2.regime' res2.tagEnv' ls).lookup? k' = some true := by
                                        simpa [ctxAfter, hRegime] using hreg
                                      simp [this])
                                have hlookup_eq :
                                    (invalidateRegimeDeps res2.regime' res2.tagEnv' ls).lookup? k' = res2.regime'.lookup? k' :=
                                  invalidateRegimeDeps_lookup_eq_lookup_of_surviving_tag res2.regime' res2.tagEnv' ls k' hkeep
                                have hreg_res2' : res2.regime'.lookup? k' = some true := by
                                  have :
                                      (invalidateRegimeDeps res2.regime' res2.tagEnv' ls).lookup? k' = some true := by
                                    simpa [ctxAfter, hRegime] using hreg
                                  simpa [hlookup_eq] using this
                                have hreg_res2 : (ctxAfter ctx' res2).regime.lookup? k' = some true := by
                                  simpa [ctxAfter, ctx'] using hreg_res2'
                                have hnotfunOld : qtOldQ.etyp.isFunctionType = false := by
                                  simp [hqtOldQ, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                                have hclean_old : qtypCleanUnder (ctxAfter ctx' res2).regime qtOldQ :=
                                  qtypCleanUnder.guard k' htag_old hreg_res2 hnotfunOld
                                have hagree_old := hagree2.1 l qtOldQ hlookup_old' hclean_old
                                cases hagree_old with
                                | both_unrealized _ _ hnone₀ hnone₁ =>
                                    exact agreeLocUnder.both_unrealized l qt hnone₀ hnone₁
                                | agree_values _ _ a0 a1 n₀' n₁' hreal₀ hreal₁ hlookup₀ hlookup₁ hagree_val =>
                                    have hEq_old : n₀' = n₁' :=
                                      agreeValueUnder_num_num_eq (qt := qtOldQ) hagree_val
                                    have hres1_clean : qtypCleanUnder (ctxAfter ctxᵢ res1).regime res1.qualType :=
                                      qtypCleanUnder.clean hres1_poison
                                    rcases
                                      resultAgreesIfClean_ref_shared_witness
                                        (predSat := predSat)
                                        (R := (ctxAfter ctxᵢ res1).regime)
                                        (μ₀ := cfg₀1.memory) (μ₁ := cfg₁1.memory)
                                        (θ₀ := θ₀1) (θ₁ := θ₁1)
                                        (qt := res1.qualType) (ls := ls)
                                        (a₀w := a₀w) (a₁w := a₁w)
                                        hRef hres_agree1 hres1_clean
                                      with ⟨lw, hlwIn, hwrite₀1, hwrite₁1⟩
                                    have hwrite₀ : θ₀2.lookup lw = some a₀w := hθext₀2.1 _ _ hwrite₀1
                                    have hwrite₁ : θ₁2.lookup lw = some a₁w := hθext₁2.1 _ _ hwrite₁1
                                    by_cases hWrite : l = lw
                                    · have ha0 : a0 = a₀w := by
                                        have : some a0 = some a₀w := by
                                          calc
                                            some a0 = θ₀2.lookup l := by symm; exact hreal₀
                                            _ = some a₀w := by simpa [hWrite] using hwrite₀
                                        exact Option.some.inj this
                                      have ha1 : a1 = a₁w := by
                                        have : some a1 = some a₁w := by
                                          calc
                                            some a1 = θ₁2.lookup l := by symm; exact hreal₁
                                            _ = some a₁w := by simpa [hWrite] using hwrite₁
                                        exact Option.some.inj this
                                      have hlookup₀_final : cf₀.memory.lookup a0 = some n₀ := by
                                        rw [hmem₀, ha0]
                                        simp [Memory.lookup]
                                      have hlookup₁_final : cf₁.memory.lookup a1 = some n₁ := by
                                        rw [hmem₁, ha1]
                                        simp [Memory.lookup]
                                      have hnotfun_rhs : res2.qualType.etyp.isFunctionType = false := by
                                        simp [hInt, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                                      have hclean_rhs : qtypCleanUnder (ctxAfter ctx' res2).regime res2.qualType :=
                                        qtypCleanUnder.guard k' htag_rhs hreg_res2 hnotfun_rhs
                                      have hagree_rhs :
                                          agreeValueUnder predSat (ctxAfter ctx' res2).regime
                                            cfg₀2.memory cfg₁2.memory θ₀2 θ₁2
                                            res2.qualType (Value.num n₀) (Value.num n₁) :=
                                        hres_agree2 hclean_rhs
                                      have hEq_write : n₀ = n₁ :=
                                        agreeValueUnder_num_num_eq (qt := res2.qualType) hagree_rhs
                                      have hagree_qt_final :
                                          agreeValueUnder predSat (ctxAfter ctxᵢ res).regime
                                            cf₀.memory cf₁.memory θ₀2 θ₁2
                                            qt (Value.num n₀) (Value.num n₁) := by
                                        refine agreeValueUnder.withPred_true_eq k' htag hreg hnotfun hnotref_qt ?_
                                        simp [hEq_write]
                                      exact
                                        agreeLocUnder.agree_values l qt a0 a1 n₀ n₁
                                          hreal₀ hreal₁ hlookup₀_final hlookup₁_final
                                          hagree_qt_final
                                    · have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀1wf
                                      have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁1wf
                                      have ha0_ne : a0 ≠ a₀w := by
                                        intro ha0
                                        apply hWrite
                                        have hlookup_lw : θ₀2.lookup lw = some a0 := by
                                          simpa [ha0] using hwrite₀
                                        exact hθ₀2wf _ _ _ hreal₀ hlookup_lw
                                      have ha1_ne : a1 ≠ a₁w := by
                                        intro ha1
                                        apply hWrite
                                        have hlookup_lw : θ₁2.lookup lw = some a1 := by
                                          simpa [ha1] using hwrite₁
                                        exact hθ₁2wf _ _ _ hreal₁ hlookup_lw
                                      have hlookup₀_final : cf₀.memory.lookup a0 = some n₀' := by
                                        rw [hmem₀]
                                        have hcmp : compare a₀w a0 ≠ Ordering.eq := by
                                          intro hce
                                          have : a₀w = a0 := (Nat.compare_eq_eq).1 hce
                                          exact ha0_ne this.symm
                                        simpa [Memory.lookup, Std.ExtTreeMap.getElem?_insert, hcmp] using hlookup₀
                                      have hlookup₁_final : cf₁.memory.lookup a1 = some n₁' := by
                                        rw [hmem₁]
                                        have hcmp : compare a₁w a1 ≠ Ordering.eq := by
                                          intro hce
                                          have : a₁w = a1 := (Nat.compare_eq_eq).1 hce
                                          exact ha1_ne this.symm
                                        simpa [Memory.lookup, Std.ExtTreeMap.getElem?_insert, hcmp] using hlookup₁
                                      have hagree_qt_final :
                                          agreeValueUnder predSat (ctxAfter ctxᵢ res).regime
                                            cf₀.memory cf₁.memory θ₀2 θ₁2
                                            qt (Value.num n₀') (Value.num n₁') := by
                                        refine agreeValueUnder.withPred_true_eq k' htag hreg hnotfun hnotref_qt ?_
                                        simp [hEq_old]
                                      exact
                                        agreeLocUnder.agree_values l qt a0 a1 n₀' n₁'
                                          hreal₀ hreal₁ hlookup₀_final hlookup₁_final
                                          hagree_qt_final
          · have hnot_contains : ¬ (ctxAfter ctx' res2).memEnv.contains l := by
              simpa [ctxAfter] using hcontains
            have hnone₀ : θ₀2.lookup l = none :=
              theta_not_contains_if_not_in_memEnv
                (ctx := (ctxAfter ctx' res2)) (μ := cfg₀2.memory) (ρ := cfg₀2.varEnv) (θ := θ₀2) (l := l)
                hric₀2 hnot_contains
            have hnone₁ : θ₁2.lookup l = none :=
              theta_not_contains_if_not_in_memEnv
                (ctx := (ctxAfter ctx' res2)) (μ := cfg₁2.memory) (ρ := cfg₁2.varEnv) (θ := θ₁2) (l := l)
                hric₁2 hnot_contains
            exact agreeLocUnder.both_unrealized l qt hnone₀ hnone₁
        · have hlookup_ctx2 : (ctxAfter ctx' res2).memEnv.lookup l = some qt :=
            hlookup_ctx2_of_not_mem l qt hlookup hIn
          have hagree_old := hagree2.1 l qt hlookup_ctx2 hclean_res2
          cases hagree_old with
          | both_unrealized _ _ hnone₀ hnone₁ =>
              exact agreeLocUnder.both_unrealized l qt hnone₀ hnone₁
          | agree_values _ _ a0 a1 n₀' n₁' hreal₀ hreal₁ hlookup₀ hlookup₁ hagree_val =>
              have hvloc₀ : valueHasETyp θ₀1 (Value.loc a₀w) (ETyp.ref ls) := by
                simpa [hRef] using _hvtyp₀1
              have hne0 : a0 ≠ a₀w := by
                intro haeq
                cases hvloc₀ with
                | loc hlookup_w hin_w =>
                    have hlookup_w' : θ₀2.lookup _ = some a₀w := hθext₀2.1 _ _ hlookup_w
                    have hlookup_l : θ₀2.lookup l = some a₀w := by
                      simpa [haeq] using hreal₀
                    have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀1wf
                    have hl_eq : l = _ := hθ₀2wf _ _ _ hlookup_l hlookup_w'
                    have : l ∈ ls := by simpa [hl_eq] using hin_w
                    exact hIn this
              have hvloc₁ : valueHasETyp θ₁1 (Value.loc a₁w) (ETyp.ref ls) := by
                simpa [hRef] using _hvtyp₁1
              have hne1 : a1 ≠ a₁w := by
                intro haeq
                cases hvloc₁ with
                | loc hlookup_w hin_w =>
                    have hlookup_w' : θ₁2.lookup _ = some a₁w := hθext₁2.1 _ _ hlookup_w
                    have hlookup_l : θ₁2.lookup l = some a₁w := by
                      simpa [haeq] using hreal₁
                    have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁1wf
                    have hl_eq : l = _ := hθ₁2wf _ _ _ hlookup_l hlookup_w'
                    have : l ∈ ls := by simpa [hl_eq] using hin_w
                    exact hIn this
              have hlookup₀' : cf₀.memory.lookup a0 = some n₀' := by
                rw [hmem₀]
                have hcmp : compare a₀w a0 ≠ Ordering.eq := by
                  intro hce
                  have : a₀w = a0 := (Nat.compare_eq_eq).1 hce
                  exact hne0 this.symm
                simpa [Memory.lookup, Std.ExtTreeMap.getElem?_insert, hcmp] using hlookup₀
              have hlookup₁' : cf₁.memory.lookup a1 = some n₁' := by
                rw [hmem₁]
                have hcmp : compare a₁w a1 ≠ Ordering.eq := by
                  intro hce
                  have : a₁w = a1 := (Nat.compare_eq_eq).1 hce
                  exact hne1 this.symm
                simpa [Memory.lookup, Std.ExtTreeMap.getElem?_insert, hcmp] using hlookup₁
              have hagree_val_final :
                  agreeValueUnder predSat (ctxAfter ctxᵢ res).regime cf₀.memory cf₁.memory θ₀2 θ₁2
                    qt (Value.num n₀') (Value.num n₁') := by
                have htmp :
                    agreeValueUnder predSat (ctxAfter ctxᵢ res).regime
                      (Std.ExtTreeMap.insert cfg₀2.memory a₀w n₀)
                      (Std.ExtTreeMap.insert cfg₁2.memory a₁w n₁)
                      θ₀2 θ₁2 qt (Value.num n₀') (Value.num n₁') := by
                  exact
                    agreeValueUnder_transport_insert_clean_monotone
                      (R := (ctxAfter ctx' res2).regime) (R' := (ctxAfter ctxᵢ res).regime)
                      (μ₀ := cfg₀2.memory) (μ₁ := cfg₁2.memory)
                      (θ₀ := θ₀2) (θ₁ := θ₁2) (qt := qt)
                      (v₀ := Value.num n₀') (v₁ := Value.num n₁')
                      a₀w a₁w n₀ n₁
                      (hpred_compat₀ := fun qt' v' =>
                        qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₀2 cfg₀2.memory (Std.ExtTreeMap.insert cfg₀2.memory a₀w n₀) qt' v')
                      (hpred_compat₁ := fun qt' v' =>
                        qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₁2 cfg₁2.memory (Std.ExtTreeMap.insert cfg₁2.memory a₁w n₁) qt' v')
                      hmono_res2_to_final hclean hagree_val
                simpa [hmem₀, hmem₁] using htmp
              exact
                agreeLocUnder.agree_values l qt a0 a1 n₀' n₁'
                  hreal₀ hreal₁ hlookup₀' hlookup₁'
                  hagree_val_final
      · intro x qt hlookup hclean
        have hlookup_ctx2 : (ctxAfter ctx' res2).varEnv.lookup x = some qt := by
          simpa [ctxAfter, ctx'] using hlookup
        have hclean_res2 : qtypCleanUnder (ctxAfter ctx' res2).regime qt := by
          exact
            qtypCleanUnder_of_invalidateRegimeDeps
              res2.regime' res2.tagEnv' ls (by simpa [ctxAfter, hRegime] using hclean)
        have hmono_res2_to_final :
            Regime.monotoneStep (ctxAfter ctx' res2).regime (ctxAfter ctxᵢ res).regime := by
          simpa [ctxAfter, hRegime] using
            invalidateRegimeDeps_monotone res2.regime' res2.tagEnv' ls
        have hagree_old := hagree2.2 x qt hlookup_ctx2 hclean_res2
        cases hagree_old with
        | both_none _ _ hnone₀ hnone₁ =>
            exact agreeVarUnder.both_none x qt (by simpa [hvar₀] using hnone₀) (by simpa [hvar₁] using hnone₁)
        | agree_values _ _ v₀ v₁ hlookup₀ hlookup₁ hagree_val =>
            have hagree_val_final :
                agreeValueUnder predSat (ctxAfter ctxᵢ res).regime cf₀.memory cf₁.memory θ₀2 θ₁2 qt v₀ v₁ := by
              have htmp :
                  agreeValueUnder predSat (ctxAfter ctxᵢ res).regime
                    (Std.ExtTreeMap.insert cfg₀2.memory a₀w n₀)
                    (Std.ExtTreeMap.insert cfg₁2.memory a₁w n₁)
                    θ₀2 θ₁2 qt v₀ v₁ := by
                exact
                  agreeValueUnder_transport_insert_clean_monotone
                    (R := (ctxAfter ctx' res2).regime) (R' := (ctxAfter ctxᵢ res).regime)
                    (μ₀ := cfg₀2.memory) (μ₁ := cfg₁2.memory)
                    (θ₀ := θ₀2) (θ₁ := θ₁2) (qt := qt)
                    (v₀ := v₀) (v₁ := v₁)
                    a₀w a₁w n₀ n₁
                    (hpred_compat₀ := fun qt' v' =>
                      qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₀2 cfg₀2.memory (Std.ExtTreeMap.insert cfg₀2.memory a₀w n₀) qt' v')
                    (hpred_compat₁ := fun qt' v' =>
                      qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₁2 cfg₁2.memory (Std.ExtTreeMap.insert cfg₁2.memory a₁w n₁) qt' v')
                    hmono_res2_to_final hclean hagree_val
              simpa [hmem₀, hmem₁] using htmp
            exact
              agreeVarUnder.agree_values x qt v₀ v₁
                (by simpa [hvar₀] using hlookup₀)
                (by simpa [hvar₁] using hlookup₁)
                hagree_val_final
  rcases hpost_transport with
    ⟨hTm_final, hwf_final, hric₀_final, hric₁_final, hreg_final, hcwr₀_final, hcwr₁_final, hagree_final⟩
  refine ⟨hresTm, ?_⟩
  refine ⟨θ₀2, θ₁2, hθext₀, hθext₁, ?_, ?_, hTm_final, hwf_final, ?_, hwfcf₀_final, hwfcf₁_final, hric₀_final, hric₁_final, hreg_final, hcwr₀_final, hcwr₁_final, hagree_final, ?_, ?_, ?_⟩
  · subst ho₀
    simpa [hEtyp] using valueHasETyp.unit (θ := θ₀2)
  · subst ho₁
    simpa [hEtyp] using valueHasETyp.unit (θ := θ₁2)
  · -- TagBoundedCtx
    exact typecheckExpr_preserves_TagBoundedCtx ctxᵢ (Expr.assign e1 e2) (Nat.succ (Nat.succ fuel')) res (by simpa [typecheck] using htc) htagBounded
  · refine valueConsistentWithRegime.noTag (predSat := predSat) (R := (ctxAfter ctxᵢ res).regime)
      (qt := res.qualType) (μ := cf₀.memory) (v := o₀) ?_ ?_
    · simp [qtypGuardTag, hPred]
    · rw [ho₀]
      exact closureCapturedVarsRegime_nonClosure_of_nonFunctionType
        (predSat := predSat) (R := (ctxAfter ctxᵢ res).regime) (qt := res.qualType)
        (μ := cf₀.memory) (v := Value.unit) (θ := θ₀2)
        (hvet := by simpa [hEtyp] using valueHasETyp.unit (θ := θ₀2))
        (hnotfun := by simp [hEtyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow])
  · refine valueConsistentWithRegime.noTag (predSat := predSat) (R := (ctxAfter ctxᵢ res).regime)
      (qt := res.qualType) (μ := cf₁.memory) (v := o₁) ?_ ?_
    · simp [qtypGuardTag, hPred]
    · rw [ho₁]
      exact closureCapturedVarsRegime_nonClosure_of_nonFunctionType
        (predSat := predSat) (R := (ctxAfter ctxᵢ res).regime) (qt := res.qualType)
        (μ := cf₁.memory) (v := Value.unit) (θ := θ₁2)
        (hvet := by simpa [hEtyp] using valueHasETyp.unit (θ := θ₁2))
        (hnotfun := by simp [hEtyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow])
  · intro hclean
    have hpoison : res.qualType.poison = false := by
      cases hclean with
      | clean hpoison => exact hpoison
      | guard k htag _ _ =>
          exfalso
          simp [qtypGuardTag, hPred] at htag
    subst ho₀
    subst ho₁
    refine agreeValueUnder.clean_eq_nonref_nonarrow (predSat := predSat)
      (R := (ctxAfter ctxᵢ res).regime) (μ₁ := cf₀.memory) (μ₂ := cf₁.memory)
      (θ₁ := θ₀2) (θ₂ := θ₁2) (qt := res.qualType) (v₁ := Value.unit) (v₂ := Value.unit)
      hpoison ?_ ?_ rfl
    · simp [hEtyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
    · intro href
      rcases href with ⟨ls', ht⟩
      have : ETyp.unit = ETyp.ref ls' := by
        simpa [hEtyp] using ht.symm
      cases this

-- World-free version of stepFRW_deref (simplified with sorry)

-- ═══════════════════════════════════════════════════════════════════════════
-- Assign single-run infrastructure (moved from FaultRobustnessProofs.lean)
-- ═══════════════════════════════════════════════════════════════════════════

private lemma typecheckAssign_lookup_clean_back_to_result1_of_pc_true
  (ctx : TypeContext) (e2 : Expr) (fuel : Nat)
  (result1 result2 res : TypeResult) (ls : LocSet)
  (htc2 : typecheckExpr (updateCtxFromResult ctx result1) e2 fuel = .ok result2)
  (hwf_ctx : wfTypeContext (updateCtxFromResult ctx result1))
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
      htc2 hwf_ctx hpc2 l qt_mid qt₂
      (by simpa [updateCtxFromResult] using hlookup_mid)
      hlookup₂
      hclean₂

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
  (htc1_expr : typecheckExpr ctx e1 fuel' = .ok result1)
  (htc2_expr : typecheckExpr (ctxAfter ctx result1) e2 fuel' = .ok result2)
  (hwf1 : wfTypeContext (ctxAfter ctx result1))
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
      htc2_expr hwf1 hpc_mid l qt_mid hlookup_mid
      (by
        have hcontains_in : ctx.memEnv.contains l :=
          memEnv_contains_of_lookup_some ctx.memEnv l qt_in hlookup_in
        simpa [ctxAfter] using
          typecheckExpr_mem_contains_preserved ctx e1 fuel' result1 htc1_expr l hcontains_in)
      hclean_mid
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

private lemma assign_single_run_post_transport_common
  (ctx : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (result1 result2 res : TypeResult) (ls : LocSet)
  (cfg2 cf : Config) (θ : RealizationMap) (a_w : Address) (n : Int)
  (_hpredlaws : PredSatLaws predSat tm)
  (hwfTm2 : wfTagMeaningCtx tm (ctxAfter (ctxAfter ctx result1) result2))
  (hwf2 : wfTypeContext (ctxAfter (ctxAfter ctx result1) result2))
  (hric2 : runtimeInstantiatesCtx (ctxAfter (ctxAfter ctx result1) result2) cfg2.memory cfg2.varEnv θ)
  (hreg2 : regimeConsistentWithCtx (ctxAfter (ctxAfter ctx result1) result2))
  (hRef : result1.qualType.etyp = ETyp.ref ls)
  (hvalRef : valueHasETyp θ (Value.loc a_w) result1.qualType.etyp)
  (_hθwf : wfRealizationMap θ)
  (hmem : cf.memory = Std.ExtTreeMap.insert cfg2.memory a_w n)
  (hvar : cf.varEnv = cfg2.varEnv)
  (hNextLoc : res.nextLoc' = ls.fold result2.nextLoc' (fun acc l => max acc (l + 1)))
  (_hNextTag : res.nextTag' = result2.nextTag')
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
  regimeConsistentWithCtx (ctxAfter ctx res) := by
  rcases valueHasETyp_loc_inv hvalRef with ⟨ls', lw, hRef', hwrite, hlwIn'⟩
  have hls : ls' = ls := by
    rw [hRef] at hRef'
    cases hRef'
    rfl
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
  refine ⟨?_, ?_, ?_, ?_⟩
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
  · simp only [wfTypeContext, ctxAfter]
    have hmono_base : result2.nextLoc' ≤ res.nextLoc' := by
      rw [hNextLoc]; exact locset_fold_max_ge_init ls result2.nextLoc'
    refine ⟨?_, varEnvRefLocsBounded_mono hwf2.2.1 (by simp [ctxAfter]; exact hmono_base),
             varEnvClosuresCapturedRefLocsBounded_mono hwf2.2.2 (by simp [ctxAfter]; exact hmono_base)⟩
    intro l hcontains
    have hcontains' : res.memEnv'.contains l = true := hcontains
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
          exact hwf2.1 l hOldCtx
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
    have htag_res2_R2 : tagEnvConsistentWithRegime result2.tagEnv' result2.regime' := by
      simpa [ctxAfter] using hreg2
    have htag_inv :
        tagEnvConsistentWithRegime (invalidateTagDeps result2.tagEnv' ls)
          (invalidateRegimeDeps result2.regime' result2.tagEnv' ls) :=
      tagEnvConsistentWithRegime_invalidateRegimeDeps result2.tagEnv' result2.regime' ls htag_res2_R2
    simpa [ctxAfter, htag_res, hRegime] using htag_inv

private lemma assign_single_run_post_transport_common_maskedReg
  (masked : Tag → Prop)
  (ctx : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (result1 result2 res : TypeResult) (ls : LocSet)
  (cfg2 cf : Config) (θ : RealizationMap) (a_w : Address) (n : Int)
  (_hpredlaws : PredSatLaws predSat tm)
  (hwfTm2 : wfTagMeaningCtx tm (ctxAfter (ctxAfter ctx result1) result2))
  (hwf2 : wfTypeContext (ctxAfter (ctxAfter ctx result1) result2))
  (hric2 : runtimeInstantiatesCtx (ctxAfter (ctxAfter ctx result1) result2) cfg2.memory cfg2.varEnv θ)
  (hreg2 : regimeConsistentWithCtxMasked masked (ctxAfter (ctxAfter ctx result1) result2))
  (hRef : result1.qualType.etyp = ETyp.ref ls)
  (hvalRef : valueHasETyp θ (Value.loc a_w) result1.qualType.etyp)
  (_hθwf : wfRealizationMap θ)
  (hmem : cf.memory = Std.ExtTreeMap.insert cfg2.memory a_w n)
  (hvar : cf.varEnv = cfg2.varEnv)
  (hNextLoc : res.nextLoc' = ls.fold result2.nextLoc' (fun acc l => max acc (l + 1)))
  (_hNextTag : res.nextTag' = result2.nextTag')
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
  regimeConsistentWithCtxMasked masked (ctxAfter ctx res) := by
  rcases valueHasETyp_loc_inv hvalRef with ⟨ls', lw, hRef', hwrite, hlwIn'⟩
  have hls : ls' = ls := by
    rw [hRef] at hRef'
    cases hRef'
    rfl
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
  refine ⟨?_, ?_, ?_, ?_⟩
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
  · simp only [wfTypeContext, ctxAfter]
    have hmono_base : result2.nextLoc' ≤ res.nextLoc' := by
      rw [hNextLoc]; exact locset_fold_max_ge_init ls result2.nextLoc'
    refine ⟨?_, varEnvRefLocsBounded_mono hwf2.2.1 (by simp [ctxAfter]; exact hmono_base),
             varEnvClosuresCapturedRefLocsBounded_mono hwf2.2.2 (by simp [ctxAfter]; exact hmono_base)⟩
    intro l hcontains
    have hcontains' : res.memEnv'.contains l = true := hcontains
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
          exact hwf2.1 l hOldCtx
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
  · unfold regimeConsistentWithCtxMasked at hreg2 ⊢
    have htag_res2_R2 :
        tagEnvConsistentWithRegimeMasked masked result2.tagEnv' result2.regime' := by
      simpa [ctxAfter] using hreg2
    have htag_inv :
        tagEnvConsistentWithRegimeMasked masked (invalidateTagDeps result2.tagEnv' ls)
          (invalidateRegimeDeps result2.regime' result2.tagEnv' ls) :=
      tagEnvConsistentWithRegimeMasked_invalidateRegimeDeps
        masked result2.tagEnv' result2.regime' ls htag_res2_R2
    simpa [ctxAfter, htag_res, hRegime] using htag_inv

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
  (_hNextTag : res.nextTag' = result2.nextTag')
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
  · simp only [wfTypeContext, ctxAfter]
    have hmono_base : result2.nextLoc' ≤ res.nextLoc' := by
      rw [hNextLoc]; exact locset_fold_max_ge_init ls result2.nextLoc'
    refine ⟨?_, varEnvRefLocsBounded_mono hwf2.2.1 (by simp [ctxAfter]; exact hmono_base),
             varEnvClosuresCapturedRefLocsBounded_mono hwf2.2.2 (by simp [ctxAfter]; exact hmono_base)⟩
    intro l hcontains
    have hcontains' : res.memEnv'.contains l = true := hcontains
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
          exact hwf2.1 l hOldCtx
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
    have htag_res2_R2 : tagEnvConsistentWithRegime result2.tagEnv' result2.regime' := by
      simpa [ctxAfter] using hreg2
    have htag_inv :
        tagEnvConsistentWithRegime (invalidateTagDeps result2.tagEnv' ls)
          (invalidateRegimeDeps result2.regime' result2.tagEnv' ls) :=
      tagEnvConsistentWithRegime_invalidateRegimeDeps result2.tagEnv' result2.regime' ls htag_res2_R2
    simpa [ctxAfter, htag_res, hRegime] using htag_inv
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

private lemma consistentWithRegime_assign_post_transport
  (predSat : PredSat) (tm : TagMeaning) :
  AssignCtxConsPostTransport regimeConsistentWithCtx
    (fun ctx μ ρ θ => consistentWithRegime predSat ctx.regime ctx μ ρ θ)
    predSat tm := by
  intro ctx result1 result2 res ls cfg2 cf θ a_w n
    hpredlaws hwfTm2 hwf2 hric2 hreg2 hcwr2
    hRef hvalRef hθwf hmem hvar hNextLoc hNextTag hRegime hmem_res htag_res hpc
  simpa using
    assign_single_run_post_transport_pc_true
      (ctx := ctx) (predSat := predSat) (tm := tm)
      (result1 := result1) (result2 := result2) (res := res) (ls := ls)
      (cfg2 := cfg2) (cf := cf) (θ := θ) (a_w := a_w) (n := n)
      hpredlaws hwfTm2 hwf2 hric2 hreg2 hcwr2
      hRef hvalRef hθwf hmem hvar hNextLoc hNextTag hRegime hmem_res htag_res hpc

private lemma consistentWithRegimeMasked_assign_post_transport
  (masked : Tag → Prop) (predSat : PredSat) (tm : TagMeaning) :
  AssignCtxConsPostTransport regimeConsistentWithCtx
    (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
    predSat tm := by
  intro ctx result1 result2 res ls cfg2 cf θ a_w n
    hpredlaws hwfTm2 hwf2 hric2 hreg2 hcwr2
    hRef hvalRef hθwf hmem hvar hNextLoc hNextTag hRegime hmem_res htag_res hpc
  rcases valueHasETyp_loc_inv hvalRef with ⟨ls', lw, hRef', hwrite, hlwIn'⟩
  have hls : ls' = ls := by
    rw [hRef] at hRef'
    cases hRef'
    rfl
  have hlwIn : lw ∈ ls := by
    simpa [hls] using hlwIn'
  have hcommon :=
    assign_single_run_post_transport_common
      (ctx := ctx) (predSat := predSat) (tm := tm)
      (result1 := result1) (result2 := result2) (res := res) (ls := ls)
      (cfg2 := cfg2) (cf := cf) (θ := θ) (a_w := a_w) (n := n)
      hpredlaws hwfTm2 hwf2 hric2 hreg2
      hRef hvalRef hθwf hmem hvar hNextLoc hNextTag hRegime hmem_res htag_res hpc
  rcases hcommon with ⟨hTm_final, hwf_final, hric_final, hreg_final⟩
  have hqtypPredHolds_mem :
      ∀ (qt : QTyp) (v : Value),
        qtypPredHolds predSat qt cfg2.memory v ↔
          qtypPredHolds predSat qt cf.memory v := by
    intro qt v
    exact qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ cfg2.memory cf.memory qt v
  have hctxCons_final :
      consistentWithRegimeMasked masked predSat
        (ctxAfter ctx res).regime (ctxAfter ctx res) cf.memory cf.varEnv θ := by
    unfold consistentWithRegimeMasked
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
            | inl hmasked =>
                exact Or.inl hmasked
            | inr hloc =>
                cases hloc with
                | noPred_ok hnp =>
                    simp [hnp] at hguard
                | guardOnly_ok k' hgo =>
                    exact Or.inr (locsRegime.guardOnly_ok (l, qt) k' hgo)
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
                    exact Or.inr <|
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
        | inl hmasked =>
            exact Or.inl hmasked
        | inr hvars =>
            cases hvars with
            | noPred_ok hnp =>
                exact Or.inr (varsRegime.noPred_ok (x, qt) hnp)
            | guardOnly_ok k' hgo =>
                exact Or.inr (varsRegime.guardOnly_ok (x, qt) k' hgo)
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
                exact Or.inr <|
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
            closureCapturedVarsRegimeMasked masked predSat (ctxAfter ctx res).regime qt cfg2.memory θ v :=
          closureCapturedVarsRegimeMasked_monotone hmono_res2_to_final hcap
        exact closureCapturedVarsRegimeMasked_transport_μ hqtypPredHolds_mem hcap_final_regime
  exact ⟨hTm_final, hwf_final, hric_final, hreg_final, hctxCons_final⟩

private lemma consistentWithRegimeMasked_assign_post_transport_maskedReg
  (masked : Tag → Prop) (predSat : PredSat) (tm : TagMeaning) :
  AssignCtxConsPostTransport (regimeConsistentWithCtxMasked masked)
    (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
    predSat tm := by
  intro ctx result1 result2 res ls cfg2 cf θ a_w n
    hpredlaws hwfTm2 hwf2 hric2 hreg2 hcwr2
    hRef hvalRef hθwf hmem hvar hNextLoc hNextTag hRegime hmem_res htag_res hpc
  rcases valueHasETyp_loc_inv hvalRef with ⟨ls', lw, hRef', hwrite, hlwIn'⟩
  have hls : ls' = ls := by
    rw [hRef] at hRef'
    cases hRef'
    rfl
  have hlwIn : lw ∈ ls := by
    simpa [hls] using hlwIn'
  have hcommon :=
    assign_single_run_post_transport_common_maskedReg
      (masked := masked)
      (ctx := ctx) (predSat := predSat) (tm := tm)
      (result1 := result1) (result2 := result2) (res := res) (ls := ls)
      (cfg2 := cfg2) (cf := cf) (θ := θ) (a_w := a_w) (n := n)
      hpredlaws hwfTm2 hwf2 hric2 hreg2
      hRef hvalRef hθwf hmem hvar hNextLoc hNextTag hRegime hmem_res htag_res hpc
  rcases hcommon with ⟨hTm_final, hwf_final, hric_final, hreg_final⟩
  have hqtypPredHolds_mem :
      ∀ (qt : QTyp) (v : Value),
        qtypPredHolds predSat qt cfg2.memory v ↔
          qtypPredHolds predSat qt cf.memory v := by
    intro qt v
    exact qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ cfg2.memory cf.memory qt v
  have hctxCons_final :
      consistentWithRegimeMasked masked predSat
        (ctxAfter ctx res).regime (ctxAfter ctx res) cf.memory cf.varEnv θ := by
    unfold consistentWithRegimeMasked
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
            | inl hmasked =>
                exact Or.inl hmasked
            | inr hloc =>
                cases hloc with
                | noPred_ok hnp =>
                    exact Or.inr (locsRegime.noPred_ok (l, qt) hnp)
                | guardOnly_ok k' hgo =>
                    exact Or.inr (locsRegime.guardOnly_ok (l, qt) k' hgo)
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
                    exact Or.inr <|
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
        | inl hmasked =>
            exact Or.inl hmasked
        | inr hvars =>
            cases hvars with
            | noPred_ok hnp =>
                exact Or.inr (varsRegime.noPred_ok (x, qt) hnp)
            | guardOnly_ok k' hgo =>
                exact Or.inr (varsRegime.guardOnly_ok (x, qt) k' hgo)
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
                exact Or.inr <|
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
            closureCapturedVarsRegimeMasked masked predSat (ctxAfter ctx res).regime qt cfg2.memory θ v :=
          closureCapturedVarsRegimeMasked_monotone hmono_res2_to_final hcap
        exact closureCapturedVarsRegimeMasked_transport_μ hqtypPredHolds_mem hcap_final_regime
  exact ⟨hTm_final, hwf_final, hric_final, hreg_final, hctxCons_final⟩

private lemma assign_result_valueConsistentWithRegime
  (ctx : TypeContext) (predSat : PredSat) (res : TypeResult) (cf : Config)
  (θ : RealizationMap)
  (hPred : res.qualType.pred = Predicate.noPred)
  (hEtyp : res.qualType.etyp = ETyp.unit) :
  valueConsistentWithRegime predSat (ctxAfter ctx res).regime
    res.qualType cf.memory θ Value.unit := by
  refine
    valueConsistentWithRegime.noTag
      (predSat := predSat) (R := (ctxAfter ctx res).regime)
      (qt := res.qualType) (μ := cf.memory) (v := Value.unit)
      ?_ ?_
  · simp [qtypGuardTag, hPred]
  · exact
      closureCapturedVarsRegime_nonClosure_of_nonFunctionType
        (by simpa [hEtyp] using valueHasETyp.unit (θ := θ))
        (by simp [hEtyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow])

private lemma assign_result_valueConsistentWithRegimeMasked
  (masked : Tag → Prop)
  (ctx : TypeContext) (predSat : PredSat) (res : TypeResult) (cf : Config)
  (θ : RealizationMap)
  (hPred : res.qualType.pred = Predicate.noPred)
  (hEtyp : res.qualType.etyp = ETyp.unit) :
  valueConsistentWithRegimeMasked masked predSat (ctxAfter ctx res).regime
    res.qualType cf.memory θ Value.unit := by
  refine
    valueConsistentWithRegimeMasked.noTag
      (qt := res.qualType) (μ := cf.memory) (v := Value.unit)
      ?_ ?_
  · simp [qtypGuardTag, hPred]
  · exact
      closureCapturedVarsRegimeMasked_nonClosure_of_nonFunctionType
        (by simpa [hEtyp] using valueHasETyp.unit (θ := θ))
        (by simp [hEtyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow])

private lemma stepFRSingleRunFinalCleanPcTrue_assign_parametric
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
  (ctx : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH :
    StepFRSingleRunFinalCleanPcTrueWithCtxValCons_IH
      CtxCons ValCons predSat tm (Nat.succ (Nat.succ fuel')))
  (hCtxConsPost : AssignCtxConsPostTransport regimeConsistentWithCtx CtxCons predSat tm)
  (hValConsResult : AssignResultValCons ValCons)
  (htc : typecheck ctx (Expr.assign e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFRSingleRunFinalCleanPcTrueWithCtxValCons
    CtxCons ValCons ctx (Expr.assign e1 e2) res predSat tm := by
  classical
  have htc' : typecheckAssign ctx e1 e2 (Nat.succ fuel') = .ok res := by
    simpa [typecheck, typecheckExpr] using htc
  obtain ⟨result1, result2, ls, htc1, hRef, htc2, hInt, hNextLoc, hNextTag, hRegime, hEtyp, hPoison, hPred⟩ :=
    typecheckAssign_structure ctx e1 e2 (Nat.succ fuel') res htc'
  have htc1_expr : typecheckExpr ctx e1 fuel' = .ok result1 := by
    simpa [Nat.succ_sub_one] using htc1
  have htc2_expr_raw :
      typecheckExpr
         
          { ctx with
            memEnv := result1.memEnv', tagEnv := result1.tagEnv',
            nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }
          e2 fuel' = .ok result2 := by
    simpa [Nat.succ_sub_one] using htc2
  have htc1' : typecheck ctx e1 fuel' = .ok result1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have htc2' : typecheck (ctxAfter ctx result1) e2 fuel' = .ok result2 := by
    simpa [typecheck, ctxAfter] using htc2_expr_raw
  intro hpredlaws hwfTm μ ρ θ cf o hθwf hwf hric hregCtx hctxCons a pm hwfcfg ht hpc
  have hinv := terminatesTo_assign_inv' e1 e2
    { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o ht
  rcases hinv with ⟨cfg1, cfg2, aw, n, ht_e1, ht_e2, ho, hmem, hvar, _hnext, _hpm⟩
  have hIH1 := IH fuel' (by simpa using Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 ctx hwfTm result1 htc1'
  have hTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1) :=
    typecheckExpr_preserves_wfTagMeaningCtx tm ctx e1 fuel' result1 hwfTm htc1'
  have hwf1 : wfTypeContext (ctxAfter ctx result1) :=
    wfTypeContext_of_wfTypeResult ctx result1
      (typecheckExpr_preserves_wfTypeResult ctx e1 fuel' result1 hwf htc1')
      hwf (typecheck_nextLoc_mono ctx e1 fuel' result1 htc1')
  have hreg1 : regimeConsistentWithCtx (ctxAfter ctx result1) :=
    typecheckExpr_preserves_regimeConsistentWithCtx ctx e1 fuel' result1 hregCtx htc1'
  have hwfcfg1 : wfConfig cfg1 := by
    exact (wfConfig_preserved e1 _ cfg1 (Value.loc aw) ht_e1 hwfcfg).1
  rcases
    hIH1 hpredlaws hwfTm μ ρ θ cfg1 (Value.loc aw)
      hθwf hwf hric hregCtx hctxCons a pm hwfcfg ht_e1 hpc
    with ⟨θ1, hθext1, hvloc1, hric1, hctxCons1, _hvalc1, hpres1, _hfresh1⟩
  have hθ1wf : wfRealizationMap θ1 := hθext1.2 hθwf
  have hmono1 : Regime.monotoneStep ctx.regime result1.regime' :=
    regime_monotone ctx e1 fuel' result1 htc1'
  have hpc1 : (ctxAfter ctx result1).pc = true := by
    simpa [ctxAfter] using hpc
  have hIH2 := IH fuel' (by simpa using Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e2 (ctxAfter ctx result1) hTm1 result2 htc2'
  rcases
    hIH2 hpredlaws hTm1 cfg1.memory cfg1.varEnv θ1 cfg2 (Value.num n)
      hθ1wf hwf1 hric1 hreg1 hctxCons1
      cfg1.nextAddr cfg1.pureMode hwfcfg1 ht_e2 hpc1
    with ⟨θ2, hθext2, hvnum2, hric2, hctxCons2, _hvalc2, hpres2, _hfresh2⟩
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
  have hTm2 : wfTagMeaningCtx tm (ctxAfter (ctxAfter ctx result1) result2) :=
    typecheckExpr_preserves_wfTagMeaningCtx tm (ctxAfter ctx result1) e2 fuel' result2 hTm1 htc2'
  have hwf2 : wfTypeContext (ctxAfter (ctxAfter ctx result1) result2) :=
    wfTypeContext_of_wfTypeResult (ctxAfter ctx result1) result2
      (typecheckExpr_preserves_wfTypeResult (ctxAfter ctx result1) e2 fuel' result2 hwf1 htc2')
      hwf1 (typecheck_nextLoc_mono (ctxAfter ctx result1) e2 fuel' result2 htc2')
  have hreg2 : regimeConsistentWithCtx (ctxAfter (ctxAfter ctx result1) result2) :=
    typecheckExpr_preserves_regimeConsistentWithCtx (ctxAfter ctx result1) e2 fuel' result2 hreg1 htc2'
  rcases
    hCtxConsPost
      (ctx := ctx) (result1 := result1) (result2 := result2) (res := res) (ls := ls)
      (cfg2 := cfg2) (cf := cf) (θ := θ2) (a_w := aw) (n := n)
      hpredlaws hTm2 hwf2 hric2 hreg2 hctxCons2
      hRef hvloc2 hθ2wf hmem hvar hNextLoc hNextTag hRegime hmem_res htag_res hpc
    with ⟨hTm_final, hwf_final, hric_final, hreg_final, hctxCons_final⟩
  have hvalc_final :
      ValCons (ctxAfter ctx res).regime res.qualType cf.memory θ2 o := by
    subst ho
    exact hValConsResult (ctx := ctx) (res := res) (cf := cf) (θ := θ2) hPred hEtyp
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
        htc1_expr
        (by simpa [ctxAfter] using htc2_expr_raw)
        hwf1
        hmem_res hRegime hpc hvloc1 hθext2 hθ2wf hric2 hmem hpres1 hpres2
  have hwfcfg_final : wfConfig cf := by
    exact (wfConfig_preserved (Expr.assign e1 e2) _ cf o ht hwfcfg).1
  have hfresh_final : FreshCleanLocsUnrealizedOneRun ctx res θ2 := by
    intro l qt hnotIn hlookup hclean
    -- First show l ∉ ls (entries at ls have poison=true/pred=noPred under pc=true → not clean)
    -- then use assign_memEnv_formula_lookup_eq_of_not_mem to get hlookup2.
    have h_not_in_ls : l ∉ ls := by
      intro h_in
      have hlookup_formula := hlookup
      rw [hmem_res] at hlookup_formula
      cases hls : Std.ExtTreeSet.toList ls with
      | nil =>
          -- If ls is empty, l ∈ ls is impossible
          have : l ∈ ls.toList := (Std.ExtTreeSet.mem_toList).2 h_in
          simp [hls] at this
      | cons x xs =>
          cases xs with
          | nil =>
              -- singleton case: x is the only element, l = x
              simp [hls] at hlookup_formula
              have hxIn : x ∈ ls := (Std.ExtTreeSet.mem_toList).1 (by simp [hls])
              have hlx : l = x := by
                have : l ∈ ls.toList := (Std.ExtTreeSet.mem_toList).2 h_in
                simp [hls] at this
                exact this
              subst hlx
              simp only [updateMemEnv, MemoryTypeEnv.lookup, ExtTreeMap.get?_eq_getElem?,
                Std.ExtTreeMap.getElem?_insert_self, Option.map] at hlookup_formula
              have hqt_eq := Option.some.inj hlookup_formula
              cases hclean with
              | clean hp => simp [← hqt_eq, joinPoison, hpc] at hp
              | guard k htag _ _ => simp [qtypGuardTag, ← hqt_eq, hpc] at htag
          | cons y ys =>
              -- multi-element case: use updateLocsetWeak
              simp [hls] at hlookup_formula
              unfold updateLocsetWeak at hlookup_formula
              set joined :=
                LocSet.fold ls
                  (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison),
                    if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred)
                  (fun (accP, accPred) l0 =>
                    match result2.memEnv'.get? l0 with
                    | some qt0 => (joinPoison accP qt0.poison, joinPredicates accPred qt0.pred)
                    | none => (accP, accPred)) with hjoined
              set finalQt : QTyp := ⟨ETyp.int, joined.1, joined.2⟩ with hfinalQt
              dsimp at hlookup_formula
              unfold LocSet.fold at hlookup_formula
              rw [Std.ExtTreeSet.foldl_eq_foldl_toList] at hlookup_formula
              have hInList : l ∈ ls.toList := (Std.ExtTreeSet.mem_toList).2 h_in
              have hlookup_final :
                  (ls.toList.foldl (fun acc l0 => updateMemEnv acc l0 finalQt) result2.memEnv').lookup l = some finalQt :=
                list_fold_updateMemEnv_lookup_eq_of_mem ls.toList result2.memEnv' l finalQt hInList rfl
              have hqt_eq : qt = finalQt :=
                Option.some.inj (hlookup_formula.symm.trans hlookup_final)
              subst hqt_eq
              have hpoison_final : finalQt.poison = true := by
                simp [finalQt, joined, hpc]
                unfold LocSet.fold
                rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
                simpa using list_fold_joinPoison_first_true result2.memEnv' ls.toList Predicate.noPred
              have hpred_final : finalQt.pred = Predicate.noPred := by
                simp [finalQt, joined, hpc]
                unfold LocSet.fold
                rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
                simpa using list_fold_joinPredicates_init_noPred result2.memEnv' ls.toList true
              cases hclean with
              | clean hp => simp [hpoison_final] at hp
              | guard k htag _ _ => simp [qtypGuardTag, hpred_final] at htag
    have hlookup_eq :=
      assign_memEnv_formula_lookup_eq_of_not_mem result2.memEnv' ls
        (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
        (if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred)
        l h_not_in_ls
    have hlookup2 : result2.memEnv'.lookup l = some qt := by
      have : res.memEnv'.lookup l = result2.memEnv'.lookup l := by
        rw [hmem_res]; exact hlookup_eq
      rwa [this] at hlookup
    have hclean2 : qtypCleanUnder result2.regime' qt := by
      cases hclean with
      | clean hp => exact qtypCleanUnder.clean hp
      | guard k htag hk hnotfun =>
          have hk2 : result2.regime'.lookup? k = some true := by
            have hkeep : (invalidateRegimeDeps result2.regime' result2.tagEnv' ls).lookup? k = some true := by
              rwa [hRegime] at hk
            have hsurv : (invalidateTagDeps result2.tagEnv' ls).contains k = true :=
              invalidateRegimeDeps_survives_of_lookup_ne_none result2.regime' result2.tagEnv' ls k (by rw [← hRegime]; simp [hk])
            rwa [invalidateRegimeDeps_lookup_eq_lookup_of_surviving_tag result2.regime' result2.tagEnv' ls k hsurv] at hkeep
          exact qtypCleanUnder.guard k htag hk2 hnotfun
    -- Two-step composition
    by_cases hcontains_mid : (ctxAfter ctx result1).memEnv.contains l
    · obtain ⟨qt_mid, hlookup_mid, hclean_mid⟩ :=
        typecheckExpr_clean_lookup_origin_of_pc_true
          (ctx := ctxAfter ctx result1) (e := e2) (fuel := fuel') (res := result2)
          htc2'
          hwf1
          hpc1
          l qt hlookup2 hcontains_mid hclean2
      have hθ1_none := _hfresh1 l qt_mid hnotIn
        (by simpa [ctxAfter] using hlookup_mid)
        (by simpa [ctxAfter] using hclean_mid)
      have hpres_loc := PreservesInheritedFinalCleanLocsOneRun.apply hpres2
        hlookup_mid hlookup2 hclean2
      cases hpres_loc with
      | both_unrealized _ hout => exact hout
      | preserve_value a n_val hin _ _ _ => simp [hθ1_none] at hin
    · exact _hfresh2 l qt hcontains_mid hlookup2 hclean2
  refine ⟨θ2, hθext, ?_, hric_final, hctxCons_final, hvalc_final, hpres_final, hfresh_final⟩
  subst ho
  simpa [hEtyp] using valueHasETyp.unit (θ := θ2)


private def StepFRAssignCtxConsPostTransport
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (predSat : PredSat) (tm : TagMeaning) : Prop :=
  AssignCtxConsPostTransport regimeConsistentWithCtx CtxCons predSat tm

private def StepFRAssignResultValCons
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop) : Prop :=
  AssignResultValCons ValCons

lemma stepFRSingleRunFinalCleanPcTrue_assign_maskedReg
  (masked : Tag → Prop)
  (ctx : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH :
    StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH
      predSat tm (Nat.succ (Nat.succ fuel'))
      masked
      (fun ctx μ ρ θ =>
        consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
      (fun R qt μ θ v =>
        valueConsistentWithRegimeMasked masked predSat R qt μ θ v))
  (htc : typecheck ctx (Expr.assign e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFRSingleRunFinalCleanPcTrueMaskedRegParam
    masked
    (fun ctx μ ρ θ =>
      consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
    (fun R qt μ θ v =>
      valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
    ctx (Expr.assign e1 e2) res predSat tm := by
  classical
  have htc' : typecheckAssign ctx e1 e2 (Nat.succ fuel') = .ok res := by
    simpa [typecheck, typecheckExpr] using htc
  obtain ⟨result1, result2, ls, htc1, hRef, htc2, hInt, hNextLoc, hNextTag, hRegime, hEtyp, hPoison, hPred⟩ :=
    typecheckAssign_structure ctx e1 e2 (Nat.succ fuel') res htc'
  have htc1_expr : typecheckExpr ctx e1 fuel' = .ok result1 := by
    simpa [Nat.succ_sub_one] using htc1
  have htc2_expr_raw :
      typecheckExpr
         
          { ctx with
            memEnv := result1.memEnv', tagEnv := result1.tagEnv',
            nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }
          e2 fuel' = .ok result2 := by
    simpa [Nat.succ_sub_one] using htc2
  have htc1' : typecheck ctx e1 fuel' = .ok result1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have htc2' : typecheck (ctxAfter ctx result1) e2 fuel' = .ok result2 := by
    simpa [typecheck, ctxAfter] using htc2_expr_raw
  intro hpredlaws hwfTm μ ρ θ cf o hθwf hwf hric hregCtx hmasked_none hctxCons a pm hwfcfg ht hpc
  have hinv := terminatesTo_assign_inv' e1 e2
    { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o ht
  rcases hinv with ⟨cfg1, cfg2, aw, n, ht_e1, ht_e2, ho, hmem, hvar, _hnext, _hpm⟩
  have hIH1 := IH fuel' (by simpa using Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 ctx hwfTm result1 htc1'
  have hTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1) :=
    typecheckExpr_preserves_wfTagMeaningCtx tm ctx e1 fuel' result1 hwfTm htc1'
  have hwf1 : wfTypeContext (ctxAfter ctx result1) :=
    wfTypeContext_of_wfTypeResult ctx result1
      (typecheckExpr_preserves_wfTypeResult ctx e1 fuel' result1 hwf htc1')
      hwf (typecheck_nextLoc_mono ctx e1 fuel' result1 htc1')
  have hreg1 : regimeConsistentWithCtxMasked masked (ctxAfter ctx result1) :=
    typecheckExpr_preserves_regimeConsistentWithCtxMasked
      (masked := masked) ctx e1 fuel' result1 hregCtx htc1'
  have hwfcfg1 : wfConfig cfg1 := by
    exact (wfConfig_preserved e1 _ cfg1 (Value.loc aw) ht_e1 hwfcfg).1
  rcases
    hIH1 hpredlaws hwfTm μ ρ θ cfg1 (Value.loc aw)
      hθwf hwf hric hregCtx hmasked_none hctxCons a pm hwfcfg ht_e1 hpc
    with ⟨θ1, hθext1, hvloc1, hric1, hctxCons1, _hvalc1, hpres1, _hfresh1⟩
  have hθ1wf : wfRealizationMap θ1 := hθext1.2 hθwf
  have hmono1 : Regime.monotoneStep ctx.regime result1.regime' :=
    regime_monotone ctx e1 fuel' result1 htc1'
  have hmasked_none1 : ∀ k, masked k → (ctxAfter ctx result1).regime.lookup? k = none := by
    intro k hk
    simpa [ctxAfter] using
      masked_lookup_none_of_monotoneStep
        (R := ctx.regime) (R' := result1.regime')
        hmasked_none hmono1 k hk
  have hpc1 : (ctxAfter ctx result1).pc = true := by
    simpa [ctxAfter] using hpc
  have hIH2 := IH fuel' (by simpa using Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e2 (ctxAfter ctx result1) hTm1 result2 htc2'
  rcases
    hIH2 hpredlaws hTm1 cfg1.memory cfg1.varEnv θ1 cfg2 (Value.num n)
      hθ1wf hwf1 hric1 hreg1 hmasked_none1 hctxCons1
      cfg1.nextAddr cfg1.pureMode hwfcfg1 ht_e2 hpc1
    with ⟨θ2, hθext2, hvnum2, hric2, hctxCons2, _hvalc2, hpres2, _hfresh2⟩
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
  have hTm2 : wfTagMeaningCtx tm (ctxAfter (ctxAfter ctx result1) result2) :=
    typecheckExpr_preserves_wfTagMeaningCtx tm (ctxAfter ctx result1) e2 fuel' result2 hTm1 htc2'
  have hwf2 : wfTypeContext (ctxAfter (ctxAfter ctx result1) result2) :=
    wfTypeContext_of_wfTypeResult (ctxAfter ctx result1) result2
      (typecheckExpr_preserves_wfTypeResult (ctxAfter ctx result1) e2 fuel' result2 hwf1 htc2')
      hwf1 (typecheck_nextLoc_mono (ctxAfter ctx result1) e2 fuel' result2 htc2')
  have hreg2 : regimeConsistentWithCtxMasked masked (ctxAfter (ctxAfter ctx result1) result2) :=
    typecheckExpr_preserves_regimeConsistentWithCtxMasked
      (masked := masked) (ctxAfter ctx result1) e2 fuel' result2 hreg1 htc2'
  rcases
    consistentWithRegimeMasked_assign_post_transport_maskedReg
      (masked := masked) (predSat := predSat) (tm := tm)
      (ctx := ctx) (result1 := result1) (result2 := result2) (res := res) (ls := ls)
      (cfg2 := cfg2) (cf := cf) (θ := θ2) (a_w := aw) (n := n)
      hpredlaws hTm2 hwf2 hric2 hreg2 hctxCons2
      hRef hvloc2 hθ2wf hmem hvar hNextLoc hNextTag hRegime hmem_res htag_res hpc
    with ⟨hTm_final, hwf_final, hric_final, hreg_final, hctxCons_final⟩
  have hvalc_final :
      valueConsistentWithRegimeMasked masked predSat
        (ctxAfter ctx res).regime res.qualType cf.memory θ2 o := by
    subst ho
    exact
      assign_result_valueConsistentWithRegimeMasked
        (masked := masked)
        (ctx := ctx) (predSat := predSat) (res := res) (cf := cf) (θ := θ2)
        hPred hEtyp
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
        htc1_expr
        (by simpa [ctxAfter] using htc2_expr_raw)
        hwf1
        hmem_res hRegime hpc hvloc1 hθext2 hθ2wf hric2 hmem hpres1 hpres2
  have hwfcfg_final : wfConfig cf := by
    exact (wfConfig_preserved (Expr.assign e1 e2) _ cf o ht hwfcfg).1
  have hfresh_final : FreshCleanLocsUnrealizedOneRun ctx res θ2 := by
    intro l qt hnotIn hlookup hclean
    have h_not_in_ls : l ∉ ls := by
      intro h_in
      have hlookup_formula := hlookup
      rw [hmem_res] at hlookup_formula
      cases hls : Std.ExtTreeSet.toList ls with
      | nil =>
          have : l ∈ ls.toList := (Std.ExtTreeSet.mem_toList).2 h_in
          simp [hls] at this
      | cons x xs =>
          cases xs with
          | nil =>
              simp [hls] at hlookup_formula
              have hlx : l = x := by
                have : l ∈ ls.toList := (Std.ExtTreeSet.mem_toList).2 h_in
                simp [hls] at this
                exact this
              subst hlx
              simp only [updateMemEnv, MemoryTypeEnv.lookup, ExtTreeMap.get?_eq_getElem?,
                Std.ExtTreeMap.getElem?_insert_self, Option.map] at hlookup_formula
              have hqt_eq := Option.some.inj hlookup_formula
              cases hclean with
              | clean hp => simp [← hqt_eq, joinPoison, hpc] at hp
              | guard k htag _ _ => simp [qtypGuardTag, ← hqt_eq, hpc] at htag
          | cons y ys =>
              simp [hls] at hlookup_formula
              unfold updateLocsetWeak at hlookup_formula
              set joined :=
                LocSet.fold ls
                  (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison),
                    if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred)
                  (fun (accP, accPred) l0 =>
                    match result2.memEnv'.get? l0 with
                    | some qt0 => (joinPoison accP qt0.poison, joinPredicates accPred qt0.pred)
                    | none => (accP, accPred)) with hjoined
              set finalQt : QTyp := ⟨ETyp.int, joined.1, joined.2⟩ with hfinalQt
              dsimp at hlookup_formula
              unfold LocSet.fold at hlookup_formula
              rw [Std.ExtTreeSet.foldl_eq_foldl_toList] at hlookup_formula
              have hInList : l ∈ ls.toList := (Std.ExtTreeSet.mem_toList).2 h_in
              have hlookup_final :
                  (ls.toList.foldl (fun acc l0 => updateMemEnv acc l0 finalQt) result2.memEnv').lookup l = some finalQt :=
                list_fold_updateMemEnv_lookup_eq_of_mem ls.toList result2.memEnv' l finalQt hInList rfl
              have hqt_eq : qt = finalQt :=
                Option.some.inj (hlookup_formula.symm.trans hlookup_final)
              subst hqt_eq
              have hpoison_final : finalQt.poison = true := by
                simp [finalQt, joined, hpc]
                unfold LocSet.fold
                rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
                simpa using list_fold_joinPoison_first_true result2.memEnv' ls.toList Predicate.noPred
              have hpred_final : finalQt.pred = Predicate.noPred := by
                simp [finalQt, joined, hpc]
                unfold LocSet.fold
                rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
                simpa using list_fold_joinPredicates_init_noPred result2.memEnv' ls.toList true
              cases hclean with
              | clean hp => simp [hpoison_final] at hp
              | guard k htag _ _ => simp [qtypGuardTag, hpred_final] at htag
    have hlookup_eq :=
      assign_memEnv_formula_lookup_eq_of_not_mem result2.memEnv' ls
        (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
        (if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred)
        l h_not_in_ls
    have hlookup2 : result2.memEnv'.lookup l = some qt := by
      have : res.memEnv'.lookup l = result2.memEnv'.lookup l := by
        rw [hmem_res]; exact hlookup_eq
      rwa [this] at hlookup
    have hclean2 : qtypCleanUnder result2.regime' qt := by
      cases hclean with
      | clean hp => exact qtypCleanUnder.clean hp
      | guard k htag hk hnotfun =>
          have hk2 : result2.regime'.lookup? k = some true := by
            have hkeep : (invalidateRegimeDeps result2.regime' result2.tagEnv' ls).lookup? k = some true := by
              rwa [hRegime] at hk
            have hsurv : (invalidateTagDeps result2.tagEnv' ls).contains k = true :=
              invalidateRegimeDeps_survives_of_lookup_ne_none result2.regime' result2.tagEnv' ls k (by rw [← hRegime]; simp [hk])
            rwa [invalidateRegimeDeps_lookup_eq_lookup_of_surviving_tag result2.regime' result2.tagEnv' ls k hsurv] at hkeep
          exact qtypCleanUnder.guard k htag hk2 hnotfun
    by_cases hcontains_mid : (ctxAfter ctx result1).memEnv.contains l
    · obtain ⟨qt_mid, hlookup_mid, hclean_mid⟩ :=
        typecheckExpr_clean_lookup_origin_of_pc_true
          (ctx := ctxAfter ctx result1) (e := e2) (fuel := fuel') (res := result2)
          htc2'
          hwf1
          hpc1
          l qt hlookup2 hcontains_mid hclean2
      have hθ1_none := _hfresh1 l qt_mid hnotIn
        (by simpa [ctxAfter] using hlookup_mid)
        (by simpa [ctxAfter] using hclean_mid)
      have hpres_loc := PreservesInheritedFinalCleanLocsOneRun.apply hpres2
        hlookup_mid hlookup2 hclean2
      cases hpres_loc with
      | both_unrealized _ hout => exact hout
      | preserve_value a n_val hin _ _ _ => simp [hθ1_none] at hin
    · exact _hfresh2 l qt hcontains_mid hlookup2 hclean2
  refine ⟨θ2, hθext, ?_, hric_final, hctxCons_final, hvalc_final, hpres_final, hfresh_final⟩
  subst ho
  simpa [hEtyp] using valueHasETyp.unit (θ := θ2)
