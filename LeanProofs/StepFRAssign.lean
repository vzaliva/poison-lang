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

lemma invalidateRegimeDeps_preserves_lookup_of_surviving_tag
    (R : Regime) (env : TagEnv) (ls : LocSet) (k : Tag) (b : Bool)
    (hR : R.lookup? k = some b)
    (hkeep : (invalidateTagDeps env ls).contains k = true) :
    (invalidateRegimeDeps R env ls).lookup? k = some b := by
  unfold Regime.lookup? at hR ⊢
  unfold invalidateRegimeDeps
  unfold invalidateTagDeps at hkeep
  split_ifs with hk
  · have hmap : R.map.get? k = some b := by
      simpa [hk] using hR
    have hmap' :
        (R.map.filter (fun k _ => (env.filter (fun _ tv => !tv.deps.any ls.contains)).contains k)).get? k = some b := by
      rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_filter']
      rw [← Std.ExtTreeMap.get?_eq_getElem?, hmap]
      simp [hkeep]
    simpa [Regime.lookup?, hk] using hmap'
  · simp [hk] at hR

lemma invalidateTagDeps_contains_true_implies_lookup_some_and_disjoint
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

lemma invalidateRegimeDeps_lookup_eq_lookup_of_surviving_tag
    (R : Regime) (env : TagEnv) (ls : LocSet) (k : Tag)
    (hkeep : (invalidateTagDeps env ls).contains k = true) :
    (invalidateRegimeDeps R env ls).lookup? k = R.lookup? k := by
  cases hR : R.lookup? k with
  | none =>
      by_cases hklt : k < R.bound
      · unfold Regime.lookup? at hR
        simp [hklt] at hR
        unfold invalidateRegimeDeps Regime.lookup?
        simp [hklt, hR]
      · unfold invalidateRegimeDeps Regime.lookup?
        simp [hklt]
  | some b =>
      have hkeepLookup :
          (invalidateRegimeDeps R env ls).lookup? k = some b :=
        invalidateRegimeDeps_preserves_lookup_of_surviving_tag R env ls k b hR hkeep
      simpa [hR] using hkeepLookup

lemma invalidateRegimeDeps_survives_of_lookup_ne_none
    (R : Regime) (env : TagEnv) (ls : LocSet) (k : Tag)
    (hlookup : (invalidateRegimeDeps R env ls).lookup? k ≠ none) :
    (invalidateTagDeps env ls).contains k = true := by
  by_cases hklt : k < R.bound
  · unfold invalidateRegimeDeps Regime.lookup? at hlookup
    have hmap : (R.map.filter (fun k _ => (invalidateTagDeps env ls).contains k)).get? k ≠ none := by
      simpa [hklt] using hlookup
    by_contra hkeep
    have hmapEq :
        (R.map.filter (fun k _ => (invalidateTagDeps env ls).contains k)).get? k =
          Option.filter (fun _ => (invalidateTagDeps env ls).contains k) (R.map.get? k) := by
      rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_filter']
      rw [← Std.ExtTreeMap.get?_eq_getElem?]
    have : (R.map.filter (fun k _ => (invalidateTagDeps env ls).contains k)).get? k = none := by
      rw [hmapEq]
      simp [hkeep]
    exact hmap this
  · unfold invalidateRegimeDeps Regime.lookup? at hlookup
    simp [hklt] at hlookup

lemma invalidateRegimeDeps_lookup_ne_none_implies_original_ne_none
    (R : Regime) (env : TagEnv) (ls : LocSet) (k : Tag)
    (hlookup : (invalidateRegimeDeps R env ls).lookup? k ≠ none) :
    R.lookup? k ≠ none := by
  have hkeep : (invalidateTagDeps env ls).contains k = true :=
    invalidateRegimeDeps_survives_of_lookup_ne_none R env ls k hlookup
  have heq :
      (invalidateRegimeDeps R env ls).lookup? k = R.lookup? k :=
    invalidateRegimeDeps_lookup_eq_lookup_of_surviving_tag R env ls k hkeep
  rwa [heq] at hlookup

lemma invalidateRegimeDeps_lookup_ne_none_implies_surviving_tag_entry
    (R : Regime) (env : TagEnv) (ls : LocSet) (k : Tag)
    (hlookup : (invalidateRegimeDeps R env ls).lookup? k ≠ none) :
    ∃ tv, env.get? k = some tv ∧ tv.deps.any ls.contains = false := by
  have hkeep : (invalidateTagDeps env ls).contains k = true :=
    invalidateRegimeDeps_survives_of_lookup_ne_none R env ls k hlookup
  exact invalidateTagDeps_contains_true_implies_lookup_some_and_disjoint env ls k hkeep

lemma regime_lookup_ne_none_or_false_tag_of_invalidate_lookup
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

lemma qtypCleanUnder_of_monotone
    {R R' : Regime} (hmono : Regime.monotoneStep R R') {qt : QTyp} :
    qtypCleanUnder R' qt → qtypCleanUnder R qt := by
  intro hclean
  cases hclean with
  | clean hpoison =>
      exact qtypCleanUnder.clean hpoison
  | guard k htag hreg hnotfun =>
      have hkR : R.lookup? k ≠ none := hmono.2.2 k (by simp [hreg])
      cases hk : R.lookup? k with
      | none =>
          exact (hkR hk).elim
      | some b =>
          have hcases : R'.lookup? k = some b ∨ R'.lookup? k = none := hmono.2.1 k b hk
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

lemma qtypCleanUnder_of_invalidateRegimeDeps
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

lemma agreeValueUnder_transport_memory
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

lemma agreeValueUnder_clean_monotoneRegime_public
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

lemma agreeValueUnder_transport_insert_clean_monotone
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

lemma agreeOnClean_transport_assign_final_of_split
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

lemma resultAgreesIfClean_ref_shared_witness
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

lemma agreeValueUnder_num_num_eq
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

lemma tagEnvConsistentWithRegime_invalidateRegimeDeps
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
  unfold invalidateRegimeDeps
  dsimp [Regime.lookup?] at hkR
  split_ifs at hkR with hklt
  · have hcontains : (invalidateTagDeps tagEnv ls).contains k = true := by
      simp only [Std.ExtTreeMap.contains_eq_isSome_getElem?]
      rw [← Std.ExtTreeMap.get?_eq_getElem?, hget]
      rfl
    have hmap :
        (R.map.filter (fun k _ => (invalidateTagDeps tagEnv ls).contains k)).get? k = some true := by
      simp [Std.ExtTreeMap.get?_eq_getElem?, hcontains, hkR]
    simp [Regime.lookup?, hklt]
    constructor
    · exact hkR
    · exact hcontains

lemma updateLocsetWeak_contains_of_contains
    (env : MemoryTypeEnv) (ls : LocSet) (storedPoison : Poison) (storedPred : Predicate)
    (l : Loc) (h : env.contains l = true) :
    (updateLocsetWeak env ls storedPoison storedPred).contains l = true := by
  unfold updateLocsetWeak
  set joined :=
    LocSet.fold ls (storedPoison, storedPred) (fun (accP, accPred) l =>
      match env.get? l with
      | some qt => (joinPoison accP qt.poison, joinPredicates accPred qt.pred)
      | none => (accP, accPred))
  set finalQt : QTyp := ⟨ETyp.int, joined.1, joined.2⟩
  dsimp
  unfold LocSet.fold
  rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
  exact list_fold_updateMemEnv_contains_of_contains ls.toList env l finalQt h

lemma assign_memEnv_formula_contains_of_contains
    (env : MemoryTypeEnv) (ls : LocSet) (storedPoison : Poison) (storedPred : Predicate)
    (l : Loc) (h : env.contains l = true) :
    (match Std.ExtTreeSet.toList ls with
      | [l0] => updateMemEnv env l0 { etyp := ETyp.int, poison := storedPoison, pred := storedPred }
      | _ => updateLocsetWeak env ls storedPoison storedPred).contains l = true := by
  cases hls : Std.ExtTreeSet.toList ls with
  | nil =>
      simp
      exact updateLocsetWeak_contains_of_contains env ls storedPoison storedPred l h
  | cons x xs =>
      cases xs with
      | nil =>
          simp
          exact updateMemEnv_contains_of_contains env x l { etyp := ETyp.int, poison := storedPoison, pred := storedPred } h
      | cons y ys =>
          simp
          exact updateLocsetWeak_contains_of_contains env ls storedPoison storedPred l h

-- updateLocsetWeak_contains_eq_or_mem: moved to TypeSafety.lean
-- assign_memEnv_formula_contains_eq_or_mem: moved to TypeSafety.lean

lemma updateLocsetWeak_lookup_eq_of_not_mem
    (env : MemoryTypeEnv) (ls : LocSet) (storedPoison : Poison) (storedPred : Predicate)
    (l : Loc) (hnot : l ∉ ls) :
    (updateLocsetWeak env ls storedPoison storedPred).lookup l = env.lookup l := by
  unfold updateLocsetWeak
  set joined :=
    LocSet.fold ls (storedPoison, storedPred) (fun (accP, accPred) l =>
      match env.get? l with
      | some qt => (joinPoison accP qt.poison, joinPredicates accPred qt.pred)
      | none => (accP, accPred))
  set finalQt : QTyp := ⟨ETyp.int, joined.1, joined.2⟩
  dsimp
  unfold LocSet.fold
  rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
  have hnotList : l ∉ ls.toList := by
    intro hmem
    exact hnot ((Std.ExtTreeSet.mem_toList).1 hmem)
  exact
    list_fold_updateMemEnv_lookup_eq_of_not_mem
      ls.toList env l finalQt hnotList

lemma assign_memEnv_formula_lookup_eq_of_not_mem
    (env : MemoryTypeEnv) (ls : LocSet) (storedPoison : Poison) (storedPred : Predicate)
    (l : Loc) (hnot : l ∉ ls) :
    (match Std.ExtTreeSet.toList ls with
      | [l0] => updateMemEnv env l0 { etyp := ETyp.int, poison := storedPoison, pred := storedPred }
      | _ => updateLocsetWeak env ls storedPoison storedPred).lookup l = env.lookup l := by
  cases hls : Std.ExtTreeSet.toList ls with
  | nil =>
      simp
      exact updateLocsetWeak_lookup_eq_of_not_mem env ls storedPoison storedPred l hnot
  | cons x xs =>
      cases xs with
      | nil =>
          have hxInList : x ∈ ls.toList := by simp [hls]
          have hxIn : x ∈ ls := (Std.ExtTreeSet.mem_toList).1 hxInList
          have hneq : l ≠ x := by
            intro hEq
            exact hnot (by simpa [hEq] using hxIn)
          simp [MemoryTypeEnv_lookup_updateMemEnv_ne
            (Γ := env) (l := x) (l' := l)
            (qt := { etyp := ETyp.int, poison := storedPoison, pred := storedPred }) hneq]
      | cons y ys =>
          simp
          exact updateLocsetWeak_lookup_eq_of_not_mem env ls storedPoison storedPred l hnot

/--
If every `tagEnv` entry at tag `k` depends on locations from `ls`, then
`invalidateRegimeDeps` drops `k` from the regime.
-/
lemma assign_updated_new_guardClosure_implies_invalidated_regime_none
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

lemma typecheckIf_ioFree_ok_pred_noPred
    (ctx : TypeContext) (e1 e2 e3 : Expr) (fuel : Nat) (res : TypeResult)
    (htc : typecheckIf .ioFree ctx e1 e2 e3 fuel = .ok res) :
    res.qualType.pred = Predicate.noPred := by
  cases fuel with
  | zero =>
      simp [typecheckIf] at htc
  | succ fuel' =>
      have htc0 : typecheckIf .ioFree ctx e1 e2 e3 (Nat.succ fuel') = .ok res := by
        simpa using htc
      have heq : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by
        native_decide
      unfold typecheckIf at htc
      cases hmatch : matchGuard e1 ctx.memEnv ctx.varEnv fuel' with
      | error err =>
          exact typecheckIf_standard_pred_noPred ctx e1 e2 e3 (Nat.succ fuel') res htc0 ⟨err, hmatch⟩
      | ok kd =>
          rcases kd with ⟨k, deps⟩
          cases hreg : ctx.regime.lookup? k with
          | some b =>
              cases b with
              | true =>
                  simp [hmatch, hreg, heq, bind, Except.bind] at htc
                  cases htc1 : typecheckExpr .ioFree { ctx with pureCtx := true } e1 fuel' with
                  | error err =>
                      simp [htc1] at htc
                  | ok res1 =>
                      simp [htc1] at htc
                      cases hq1 : res1.qualType with
                      | mk etyp1 p1 pred1 =>
                          simp [hq1] at htc
                          by_cases hbool : etyp1 = ETyp.bool
                          · simp [hbool] at htc
                            cases htc2 : typecheckExpr .ioFree { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ } e2 fuel' with
                            | error err =>
                                simp [htc2] at htc
                                cases htc
                            | ok res2 =>
                                simp [htc2, pure, Except.pure] at htc
                                cases hq2 : res2.qualType with
                                | mk etyp2 p2 pred2 =>
                                    simp [hq2] at htc
                                    cases htc
                                    rfl
                          · simp [hbool] at htc
              | false =>
                  simp [hmatch, hreg, heq, bind, Except.bind] at htc
                  cases htc1 : typecheckExpr .ioFree { ctx with pureCtx := true } e1 fuel' with
                  | error err =>
                      simp [htc1] at htc
                  | ok res1 =>
                      simp [htc1] at htc
                      cases hq1 : res1.qualType with
                      | mk etyp1 p1 pred1 =>
                          simp [hq1] at htc
                          by_cases hbool : etyp1 = ETyp.bool
                          · simp [hbool] at htc
                            cases htc3 : typecheckExpr .ioFree { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩ } e3 fuel' with
                            | error err =>
                                simp [htc3] at htc
                                cases htc
                            | ok res3 =>
                                simp [htc3, pure, Except.pure] at htc
                                cases hq3 : res3.qualType with
                                | mk etyp3 p3 pred3 =>
                                    simp [hq3] at htc
                                    cases htc
                                    rfl
                          · simp [hbool] at htc
          | none =>
              simp [hmatch, hreg, bind, Except.bind] at htc
              cases htc1 : typecheckExpr .ioFree { ctx with pureCtx := true } e1 fuel' with
              | error err =>
                  simp [htc1] at htc
              | ok res1 =>
                  simp [htc1] at htc
                  cases hq1 : res1.qualType with
                  | mk etyp1 p1 pred1 =>
                      simp [hq1] at htc
                      by_cases hbool : etyp1 = ETyp.bool
                      · simp [hbool, pure, Except.pure] at htc
                        let branchPc := joinPoison ctx.pc p1
                        let ctxTrue := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩, pc := branchPc }
                        cases htc2 : typecheckExpr .ioFree ctxTrue e2 fuel' with
                        | error err =>
                            rw [htc2] at htc
                            simp at htc
                        | ok res2 =>
                            rw [htc2] at htc
                            simp at htc
                            cases hq2 : res2.qualType with
                            | mk etyp2 p2 pred2 =>
                                simp [hq2] at htc
                                let ctxFalse := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩, pc := branchPc }
                                let ctxFalse' := { ctxFalse with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
                                cases htc3 : typecheckExpr .ioFree ctxFalse' e3 fuel' with
                                | error err =>
                                    rw [htc3] at htc
                                    simp at htc
                                | ok res3 =>
                                    rw [htc3] at htc
                                    simp at htc
                                    cases hq3 : res3.qualType with
                                    | mk etyp3 p3 pred3 =>
                                        simp [hq3] at htc
                                        by_cases hcompat : beqETypSignature etyp2 etyp3 = false
                                        · simp [hcompat] at htc
                                        · have hcompat' : beqETypSignature etyp2 etyp3 = true := by
                                            cases hbeq : beqETypSignature etyp2 etyp3 <;> simp_all
                                          simp [hcompat'] at htc
                                          cases htc
                                          rfl
                      · simp [hbool] at htc

lemma typecheckVar_guardClosure_pred_implies_tag_absent
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

lemma typecheckDeref_guardClosure_pred_implies_tag_absent
    (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
    (htc : typecheckDeref .ioFree ctx e fuel = .ok res)
    (hpred : res.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env) :
    res.tagEnv'.get? k = none := by
  cases fuel with
  | zero =>
      simp [typecheckDeref] at htc
  | succ fuel' =>
      unfold typecheckDeref at htc
      simp [bind, Except.bind] at htc
      cases htc1 : typecheckExpr .ioFree ctx e fuel' with
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

lemma joinTagEnvs_get?_none_of_left_none
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

lemma typecheckApp_arrow_branch_guardClosure_pred_implies_tag_absent
    (ctx : TypeContext) (res : TypeResult)
    (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
    (fuel' : Nat)
    (ih :
      ∀ m < fuel' + 1 + 1,
        ∀ (ctx : TypeContext) (e : Expr) (res : TypeResult),
          typecheckExpr LeanPoison.EvalMode.ioFree ctx e m = Except.ok res →
          res.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env →
          Std.ExtTreeMap.get? res.tagEnv' k = none)
    (st1 st2 : Typ) (p p1 : Poison) (etyp2 : ETyp) (p2 : Poison) (pred2 : Predicate)
    (result1 : TypeResult)
    (tcls : List FnTClosure) (results : List TypeResult) (first : TypeResult) (rest : List TypeResult)
    (hmap :
      List.mapM
        (fun tcl =>
          applyFnTClosure LeanPoison.EvalMode.ioFree tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel')
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
                    applyFnTClosure .ioFree tcl0 st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel' = .ok first := by
                have hForall2 :
                    List.Forall₂
                      (fun tcl r => applyFnTClosure .ioFree tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel' = .ok r)
                      tcls results :=
                  List.mapM_Except_ok_implies_forall2 tcls
                    (fun tcl => applyFnTClosure .ioFree tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel')
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
                            typecheckExpr .ioFree
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
                                            body result3 htcBody (by simpa [hq3] using hpred3)
                                        simpa [hfirstEq] using hnone3
                | extern x retSpec effects capturedEnv =>
                    unfold applyFnTClosure at happly
                    cases fuel' with
                    | zero =>
                        simp at happly
                    | succ fuel'' =>
                        simp [bind, Except.bind] at happly
                        exact absurd happly
                          (Except.error_ne_ok "Extern function application forbidden in ioFree mode" first)
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

lemma typecheckApp_parrow_branch_guardClosure_pred_implies_tag_absent
    (ctx : TypeContext) (res : TypeResult)
    (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
    (fuel' : Nat)
    (ih :
      ∀ m < fuel' + 1 + 1,
        ∀ (ctx : TypeContext) (e : Expr) (res : TypeResult),
          typecheckExpr LeanPoison.EvalMode.ioFree ctx e m = Except.ok res →
          res.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env →
          Std.ExtTreeMap.get? res.tagEnv' k = none)
    (st1 st2 : Typ) (p p1 : Poison) (etyp2 : ETyp) (p2 : Poison) (pred2 : Predicate)
    (result1 : TypeResult)
    (tcls : List PFnTClosure) (results : List TypeResult) (first : TypeResult) (rest : List TypeResult)
    (hmap :
      List.mapM
        (fun tcl =>
          applyPFnTClosure LeanPoison.EvalMode.ioFree tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel')
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
                    applyPFnTClosure .ioFree tcl0 st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel' = .ok first := by
                have hForall2 :
                    List.Forall₂
                      (fun tcl r => applyPFnTClosure .ioFree tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel' = .ok r)
                      tcls results :=
                  List.mapM_Except_ok_implies_forall2 tcls
                    (fun tcl => applyPFnTClosure .ioFree tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel')
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
                            typecheckExpr .ioFree
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
                                            (PExpr.toExpr pbody) result3 htcBody (by simpa [hq3] using hpred3)
                                        simpa [hfirstEq] using hnone3
                | extern x retSpec capturedEnv =>
                    unfold applyPFnTClosure at happly
                    cases fuel' with
                    | zero =>
                        simp at happly
                    | succ fuel'' =>
                        simp [bind, Except.bind] at happly
                        exact absurd happly
                          (Except.error_ne_ok "Extern function application forbidden in ioFree mode" first)
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

lemma ioFree_guardClosure_pred_implies_tag_absent
    (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
    (htc : typecheckExpr .ioFree ctx e fuel = .ok res)
    (hpred : res.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env) :
    res.tagEnv'.get? k = none := by
  revert ctx e res htc hpred
  refine Nat.strongRecOn fuel ?_
  intro fuel ih ctx e res htc hpred
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
          have htc' : typecheckUnaryOp .ioFree ctx op e1 fuel = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckUnaryOp_structure ctx op e1 fuel res htc' with
            ⟨result1, result_etyp, htc1, hop, hmem, htag, hnextLoc, hnextTag, hreg, hetyp, hpoison, hpredNo⟩
          exfalso
          simp [hpredNo] at hpred
      | op e1 op e2 =>
          have htc' : typecheckOp .ioFree ctx e1 e2 fuel op = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckOp_structure ctx e1 e2 op fuel res htc' with
            ⟨result1, result2, result_etyp, htc1, htc2, hop, hmem, htag, hnextLoc, hnextTag, hreg, hetyp, hpoison, hpredNo⟩
          exfalso
          simp [hpredNo] at hpred
      | newRef e1 =>
          have htc' : typecheckNewRef .ioFree ctx e1 fuel = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckNewRef_structure ctx e1 fuel res htc' with
            ⟨result1, l, htc1, hl, hetyp1, hetyp, hpoison, hpredNo, hmem, htag, hnextLoc, hnextTag, hreg⟩
          exfalso
          simp [hpredNo] at hpred
      | assign e1 e2 =>
          have htc' : typecheckAssign .ioFree ctx e1 e2 fuel = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckAssign_structure ctx e1 e2 fuel res htc' with
            ⟨result1, result2, ls, htc1, href, htc2, hqt2int, hnextLoc, hnextTag, hreg, hetyp, hpoison, hpredNo⟩
          exfalso
          simp [hpredNo] at hpred
      | seq e1 e2 =>
          have htc' : typecheckSeq .ioFree ctx e1 e2 fuel = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckSeq_structure ctx e1 e2 fuel res htc' with
            ⟨result1, ctx', htc1, hctx', htc2⟩
          have hlt : fuel - 1 < Nat.succ fuel := Nat.lt_succ_of_le (Nat.sub_le fuel 1)
          exact ih (fuel - 1) hlt ctx' e2 res htc2 hpred
      | vlet x e1 e2 =>
          have htc' : typecheckVlet .ioFree ctx x e1 e2 fuel = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckVlet_structure ctx x e1 e2 fuel res htc' with
            ⟨result1, result2, ctx', htc1, hctx', htc2, hetyp, hmem, htag, hnextLoc, hnextTag, hreg, hpoison, hpredEq⟩
          have hpred2 : result2.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env := by
            simpa [hpredEq] using hpred
          have hnone2 : result2.tagEnv'.get? k = none :=
            ih (fuel - 1) (Nat.lt_succ_of_le (Nat.sub_le fuel 1)) ctx' e2 result2 htc2 hpred2
          simpa [htag] using hnone2
      | rand e1 =>
          exfalso
          have htc' : typecheckRand .ioFree ctx e1 fuel = .ok res := by
            simpa [typecheckExpr] using htc
          exact absurd htc' (typecheckRand_ioFree_impossible ctx e1 fuel res)
      | frand e1 =>
          exfalso
          have htc' : typecheckFrand .ioFree ctx e1 fuel = .ok res := by
            simpa [typecheckExpr] using htc
          exact absurd htc' (typecheckFrand_ioFree_impossible ctx e1 fuel res)
      | printString e1 =>
          exfalso
          have htc' : typecheckPrintString .ioFree ctx e1 fuel = .ok res := by
            simpa [typecheckExpr] using htc
          exact absurd htc' (typecheckPrintString_ioFree_impossible ctx e1 fuel res)
      | printInt e1 =>
          exfalso
          have htc' : typecheckPrintInt .ioFree ctx e1 fuel = .ok res := by
            simpa [typecheckExpr] using htc
          exact absurd htc' (typecheckPrintInt_ioFree_impossible ctx e1 fuel res)
      | ite e1 e2 e3 =>
          exfalso
          have htc' : typecheckIf .ioFree ctx e1 e2 e3 fuel = .ok res := by
            simpa [typecheckExpr] using htc
          have hpredNo : res.qualType.pred = Predicate.noPred :=
            typecheckIf_ioFree_ok_pred_noPred ctx e1 e2 e3 fuel res htc'
          simp [hpredNo] at hpred
      | kwhile e1 e2 =>
          exfalso
          have htc' : typecheckWhile .ioFree ctx e1 e2 fuel = .ok res := by
            simpa [typecheckExpr] using htc
          have hpredNo : res.qualType.pred = Predicate.noPred := by
            cases fuel with
            | zero =>
                simp [typecheckWhile] at htc'
            | succ fuel' =>
                unfold typecheckWhile at htc'
                cases hmatch : matchGuard e1 ctx.memEnv ctx.varEnv fuel' with
                | ok kd =>
                    rcases kd with ⟨k', deps⟩
                    simp [hmatch] at htc'
                    unfold typecheckWhileDepoison at htc'
                    cases fuel' with
                    | zero =>
                        simp at htc'
                    | succ fuel'' =>
                        simp [bind, Except.bind, pure, Except.pure] at htc'
                        cases hfix : runWhileFixpoint .ioFree ctx e1 e2 fuel'' true (some (k', deps)) with
                        | error err =>
                            simp [hfix] at htc'
                        | ok v =>
                            simp [hfix] at htc'
                            cases htc'
                            rfl
                | error err =>
                    simp [hmatch] at htc'
                    unfold typecheckWhileStd at htc'
                    cases fuel' with
                    | zero =>
                        simp at htc'
                    | succ fuel'' =>
                        simp [bind, Except.bind, pure, Except.pure] at htc'
                        cases hfix : runWhileFixpoint .ioFree ctx e1 e2 fuel'' false none with
                        | error err =>
                            simp [hfix] at htc'
                        | ok v =>
                            simp [hfix] at htc'
                            cases htc'
                            rfl
          simp [hpredNo] at hpred
      | var x =>
          have htcVar : typecheckVar ctx x = .ok res := by
            simpa [typecheckExpr] using htc
          exact
            typecheckVar_guardClosure_pred_implies_tag_absent
              ctx x res k arg_name pred_body var_env htcVar hpred
      | deref e1 =>
          have htcD : typecheckDeref .ioFree ctx e1 fuel = .ok res := by
            simpa [typecheckExpr] using htc
          exact
            typecheckDeref_guardClosure_pred_implies_tag_absent
              ctx e1 fuel res k arg_name pred_body var_env htcD hpred
      | app e1 e2 =>
          have htcA : typecheckApp .ioFree ctx e1 e2 fuel = .ok res := by
            simpa [typecheckExpr] using htc
          cases fuel with
          | zero =>
              simp [typecheckApp] at htcA
          | succ fuel' =>
              rcases
                  typecheckApp_arrow_structure_full ctx e1 e2 fuel' res (by simpa using htcA)
                with ⟨result2, result1, etyp2, p2, pred2, hq2, htc2, htc1, hcases⟩
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
                      (result1 := result1)
                      (tcls := tcls) (results := results) (first := first) (rest := rest)
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
                      (result1 := result1)
                      (tcls := tcls) (results := results) (first := first) (rest := rest)
                      hmap hresults hjoin hpred
      | externVal _ _ _ =>
          exfalso
          have heq : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by
            native_decide
          have htc' := htc
          simp [typecheckExpr, typecheckExternVal, heq] at htc'
          cases htc'
      | externFn _ _ _ _ =>
          exfalso
          have heq : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by
            native_decide
          have htc' := htc
          simp [typecheckExpr, typecheckExternFn, heq] at htc'
          cases htc'
      | externPfn _ _ _ =>
          exfalso
          have heq : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by
            native_decide
          have htc' := htc
          simp [typecheckExpr, typecheckExternPfn, heq] at htc'
          cases htc'

lemma assign_mem_formula_guardClosure_lookup_implies_rhs_pred
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
                pred := if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred }
        | _ =>
            updateLocsetWeak res2.memEnv' ls
              (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
              (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)))
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
                pred := if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred }
        | _ =>
            updateLocsetWeak res2.memEnv' ls
              (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
              (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)).lookup l = some qt := by
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
                  pred := if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred }).lookup l = some qt := by
            simpa [hls] using hlookup_formula
          subst hlEq
          simp [updateMemEnv, MemoryTypeEnv.lookup] at hlookup_single
          have hqtEq :
              qt =
                { etyp := ETyp.int
                  poison := joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison)
                  pred := if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred } := by
            simpa using hlookup_single.symm
          have hpred_stored :
              (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred) =
                Predicate.guardClosure k arg_name pred_body var_env := by
            simpa [hqtEq] using hpred
          cases hp : res1.qualType.poison with
          | false =>
              simpa [hp] using hpred_stored
          | true =>
              simp [hp] at hpred_stored
      | cons y ys =>
          have hlookup_weak :
              (updateLocsetWeak res2.memEnv' ls
                (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)).lookup l = some qt := by
            simpa [hls] using hlookup_formula
          unfold updateLocsetWeak at hlookup_weak
          set joined :=
            LocSet.fold ls
              (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison),
                if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)
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
                    if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)).2) =
                Predicate.guardClosure k arg_name pred_body var_env := by
            unfold joined at hjoined_guard
            unfold LocSet.fold at hjoined_guard
            rw [Std.ExtTreeSet.foldl_eq_foldl_toList] at hjoined_guard
            exact hjoined_guard
          have hstored :
              (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred) =
                Predicate.guardClosure k arg_name pred_body var_env :=
            fold_joinPred_guardClosure_init
              res2.memEnv' ls.toList
              (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
              (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)
              hjoined_fold
          cases hp : res1.qualType.poison with
          | false =>
              simpa [hp] using hstored
          | true =>
              simp [hp] at hstored

-- locset_fold_max_succ_ge_of_mem: moved to TypeSafety.lean

def PredRespectsTagMeaning (tm : TagMeaning) (pred : Predicate) : Prop :=
  ∀ (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
    pred = Predicate.guardClosure k arg_name pred_body var_env →
    tm.lookup k = some { argName := arg_name, body := pred_body, capEnv := var_env }

lemma qtypGuardDesc_lookup_of_predRespects_int
    (tm : TagMeaning) (poison : Poison) (pred : Predicate)
    (hpred : PredRespectsTagMeaning tm pred) :
    ∀ (k : Tag) (d : GuardDesc),
      qtypGuardDesc? { etyp := ETyp.int, poison := poison, pred := pred } = some (k, d) →
      tm.lookup k = some d := by
  intro k d hqd
  cases pred with
  | noPred =>
      simp [qtypGuardDesc?] at hqd
  | guardOnly k0 =>
      simp [qtypGuardDesc?] at hqd
  | guardClosure k0 arg_name pred_body var_env =>
      simp [qtypGuardDesc?] at hqd
      rcases hqd with ⟨hk, hd⟩
      subst hk
      subst hd
      exact hpred k0 arg_name pred_body var_env rfl

lemma QTypRespectsTagMeaning_int_of_predRespects
    (tm : TagMeaning) (poison : Poison) (pred : Predicate)
    (hpred : PredRespectsTagMeaning tm pred) :
    QTypRespectsTagMeaning tm { etyp := ETyp.int, poison := poison, pred := pred } := by
  intro qt k d hinq hqd
  have hEq : qt = { etyp := ETyp.int, poison := poison, pred := pred } :=
    QTypInQTyp_eq_of_nonFunctionTarget hinq (by
      simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow])
  subst hEq
  exact qtypGuardDesc_lookup_of_predRespects_int tm poison pred hpred k d hqd

lemma PredRespectsTagMeaning_joinPredicates
    (tm : TagMeaning) (p q : Predicate)
    (hp : PredRespectsTagMeaning tm p) :
    PredRespectsTagMeaning tm (joinPredicates p q) := by
  intro k arg_name pred_body var_env hjoin
  have hsplit :=
    joinPredicates_eq_guardClosure
      (p := p) (q := q) (k := k) (arg_name := arg_name)
      (pred_body := pred_body) (var_env := var_env) hjoin
  exact hp k arg_name pred_body var_env hsplit.1

lemma PredRespectsTagMeaning_list_fold_updateLocsetWeak
    (tm : TagMeaning) (env : MemoryTypeEnv) (xs : List Loc)
    (storedPoison : Poison) (storedPred : Predicate)
    (hinit : PredRespectsTagMeaning tm storedPred) :
    PredRespectsTagMeaning tm
      ((xs.foldl
        (fun acc l =>
          match env.get? l with
          | some qt => (joinPoison acc.1 qt.poison, joinPredicates acc.2 qt.pred)
          | none => acc)
        (storedPoison, storedPred)).2) := by
  induction xs generalizing storedPoison storedPred with
  | nil =>
      simpa using hinit
  | cons x xs ih =>
      simp [List.foldl]
      cases hget : env.get? x with
      | none =>
          have hget' : env[x]? = none := by simpa using hget
          simpa [hget'] using ih storedPoison storedPred hinit
      | some qt =>
          have hjoin : PredRespectsTagMeaning tm (joinPredicates storedPred qt.pred) :=
            PredRespectsTagMeaning_joinPredicates tm storedPred qt.pred hinit
          have hget' : env[x]? = some qt := by simpa using hget
          simpa [hget'] using ih (joinPoison storedPoison qt.poison)
            (joinPredicates storedPred qt.pred) hjoin

lemma EnvRespectsTagMeaning_updateMemEnv
    (tm : TagMeaning) (σ : VarTypeEnv) (env : MemoryTypeEnv) (l : Loc) (qt : QTyp)
    (hqt_int : qt.etyp = ETyp.int)
    (hEnv : EnvRespectsTagMeaning tm σ env)
    (hqt : QTypRespectsTagMeaning tm qt) :
    EnvRespectsTagMeaning tm σ (updateMemEnv env l qt) := by
  simpa [updateMemEnv] using
    (EnvRespectsTagMeaning_memEnv_ext tm σ env l qt hqt_int hEnv hqt)

lemma EnvRespectsTagMeaning_list_fold_updateMemEnv
    (tm : TagMeaning) (σ : VarTypeEnv) (xs : List Loc) (env : MemoryTypeEnv) (qt : QTyp)
    (hqt_int : qt.etyp = ETyp.int)
    (hEnv : EnvRespectsTagMeaning tm σ env)
    (hqt : QTypRespectsTagMeaning tm qt) :
    EnvRespectsTagMeaning tm σ
      (xs.foldl (fun acc l => updateMemEnv acc l qt) env) := by
  induction xs generalizing env with
  | nil =>
      simpa using hEnv
  | cons x xs ih =>
      have h1 : EnvRespectsTagMeaning tm σ (updateMemEnv env x qt) :=
        EnvRespectsTagMeaning_updateMemEnv tm σ env x qt hqt_int hEnv hqt
      simpa using ih (env := updateMemEnv env x qt) h1

lemma EnvRespectsTagMeaning_updateLocsetWeak
    (tm : TagMeaning) (σ : VarTypeEnv) (env : MemoryTypeEnv) (ls : LocSet)
    (storedPoison : Poison) (storedPred : Predicate)
    (hEnv : EnvRespectsTagMeaning tm σ env)
    (hpred : PredRespectsTagMeaning tm storedPred) :
    EnvRespectsTagMeaning tm σ (updateLocsetWeak env ls storedPoison storedPred) := by
  unfold updateLocsetWeak
  set joined :=
    LocSet.fold ls (storedPoison, storedPred) (fun (accP, accPred) l =>
      match env.get? l with
      | some qt => (joinPoison accP qt.poison, joinPredicates accPred qt.pred)
      | none => (accP, accPred))
  set finalQt : QTyp := ⟨ETyp.int, joined.1, joined.2⟩
  have hpred_joined : PredRespectsTagMeaning tm joined.2 := by
    unfold joined
    unfold LocSet.fold
    rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
    exact
      PredRespectsTagMeaning_list_fold_updateLocsetWeak
        tm env ls.toList storedPoison storedPred hpred
  have hfinal_qtyp : QTypRespectsTagMeaning tm finalQt := by
    unfold finalQt
    exact QTypRespectsTagMeaning_int_of_predRespects tm joined.1 joined.2 hpred_joined
  dsimp
  unfold LocSet.fold
  rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
  exact
    EnvRespectsTagMeaning_list_fold_updateMemEnv
      tm σ ls.toList env finalQt (by simp [finalQt]) hEnv hfinal_qtyp

lemma stepFR_assign
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck .ioFree ctxᵢ (Expr.assign e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ (Expr.assign e1 e2) res predSat tm := by
  classical
  have htc' : typecheckAssign .ioFree ctxᵢ e1 e2 (Nat.succ fuel') = .ok res := by
    simp [typecheck, typecheckExpr] at htc
    exact htc
  obtain ⟨res1, res2, ls, htc1, hRef, htc2, hInt, hNextLoc, hNextTag, hRegime, hEtyp, hPoison, hPred⟩ :=
    typecheckAssign_structure ctxᵢ e1 e2 (Nat.succ fuel') res htc'
  have htc1_expr : typecheckExpr .ioFree ctxᵢ e1 fuel' = .ok res1 := by
    simpa [Nat.succ_sub_one] using htc1
  have htc2_expr :
      typecheckExpr
          .ioFree
          { ctxᵢ with
            memEnv := res1.memEnv', tagEnv := res1.tagEnv',
            nextLoc := res1.nextLoc', nextTag := res1.nextTag', regime := res1.regime' }
          e2 fuel' = .ok res2 := by
    simpa [Nat.succ_sub_one] using htc2
  have htc_full := htc'
  simp [typecheckAssign, htc1_expr, htc2_expr, bind, Except.bind, pure, Except.pure] at htc_full
  have htc1' : typecheck .ioFree ctxᵢ e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  let ctx' : TypeContext := {
    ctxᵢ with
      memEnv := res1.memEnv'
      tagEnv := res1.tagEnv'
      nextLoc := res1.nextLoc'
      nextTag := res1.nextTag'
      regime := res1.regime'
  }
  have htc2' : typecheck .ioFree ctx' e2 fuel' = .ok res2 := by
    simpa [ctx', typecheck, Nat.succ_sub_one] using htc2
  intro hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ hregCtx hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  have hinv₀ := terminatesTo_assign_inv' e1 e2 { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  rcases hinv₀ with ⟨cfg₀1, cfg₀2, a₀w, n₀, ht₀_e1, ht₀_e2, ho₀, hmem₀, hvar₀, hnext₀, hpm₀⟩
  have hinv₁ := terminatesTo_assign_inv' e1 e2 { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  rcases hinv₁ with ⟨cfg₁1, cfg₁2, a₁w, n₁, ht₁_e1, ht₁_e2, ho₁, hmem₁, hvar₁, hnext₁, hpm₁⟩
  have hIH1 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 ctxᵢ hwfTm res1 htc1'
  have hstep_e1 :=
    hIH1 hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 (Value.loc a₀w) (Value.loc a₁w)
      hθ₀ hθ₁ hwf hric₀ hric₁ hregCtx hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e1 ht₁_e1
  rcases hstep_e1 with ⟨hresTm1, hstep_e1⟩
  rcases hstep_e1 with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, _hvtyp₀1, _hvtyp₁1, hTm1, hwf1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, hregCtx1, hcwr₀1, hcwr₁1, hagree1, hvc₀1, hvc₁1, hres_agree1⟩
  have hwfTm' : wfTagMeaningCtx tm ctx' := by
    simpa [ctx', ctxAfter] using hTm1
  have hIH2 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e2 ctx' hwfTm' res2 htc2'
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
  have hRbound' : regimeBounded ctx'.regime := by
    exact regimeBounded_of_monotoneStep ctxᵢ.regime res1.regime' hRbound hmono1
  have hpm₀1 : cfg₀1.pureMode = pm := by
    simpa using
      (terminatesTo_IOFree_preserves_pureMode e1
        { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cfg₀1 (Value.loc a₀w) ht₀_e1)
  have hpm₁1 : cfg₁1.pureMode = pm := by
    simpa using
      (terminatesTo_IOFree_preserves_pureMode e1
        { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cfg₁1 (Value.loc a₁w) ht₁_e1)
  have hpm_eq : cfg₁1.pureMode = cfg₀1.pureMode := by
    rw [hpm₁1, hpm₀1]
  have hcfg₁1_eq : cfg₁1 = { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode } := by
    cases cfg₁1
    simp only [Config.mk.injEq, true_and]
    exact hpm_eq
  have ht₁_e2' : terminatesTo .ioFree e2
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
      hθ₀1wf hθ₁1wf hwf_ctx' hric₀1' hric₁1' hregCtx1' hRbound' hcwr₀1' hcwr₁1' hagree1'
      cfg₀1.nextAddr cfg₁1.nextAddr cfg₀1.pureMode hwfcf₀1 hwfcf₁1' ht₀_e2 ht₁_e2'
  rcases hstep_e2 with ⟨hresTm2, hstep_e2⟩
  rcases hstep_e2 with ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, hv₀2, hv₁2, hTm2, hwf2, hwfcf₀2, hwfcf₁2, hric₀2, hric₁2, hregCtx2, hcwr₀2, hcwr₁2, hagree2, hvc₀2, hvc₁2, hres_agree2⟩
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    have hnotfun : res.qualType.etyp.isFunctionType = false := by
      simp [hEtyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
    have hguard : qtypGuardDesc? res.qualType = none := by
      simp [qtypGuardDesc?, hPred]
    intro qt' k d hinq hqd
    exact (QTypRespectsTagMeaning_of_nonFunction_noGuard tm res.qualType hnotfun hguard) hinq hqd
  have hθext₀ : wfExtendsMap θ₀ θ₀2 := wfExtendsMap_trans hθext₀1 hθext₀2
  have hθext₁ : wfExtendsMap θ₁ θ₁2 := wfExtendsMap_trans hθext₁1 hθext₁2
  have hwfcf₀_final : wfConfig cf₀ := (wfConfig_preserved .ioFree (Expr.assign e1 e2) _ cf₀ o₀ ht₀ hwfcfg₀).1
  have hwfcf₁_final : wfConfig cf₁ := (wfConfig_preserved .ioFree (Expr.assign e1 e2) _ cf₁ o₁ ht₁ hwfcfg₁).1
  have hassign_eq :
      { qualType := { etyp := ETyp.unit, poison := joinPoison ctxᵢ.pc res1.qualType.poison, pred := Predicate.noPred }
        memEnv' :=
          match Std.ExtTreeSet.toList ls with
          | [l] =>
              updateMemEnv res2.memEnv' l
                { etyp := ETyp.int
                  poison := joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison)
                  pred := if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred }
          | _ =>
              updateLocsetWeak res2.memEnv' ls
                (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)
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
                pred := if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred }
        | _ =>
            updateLocsetWeak res2.memEnv' ls
              (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
              (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred) := by
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
        if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred
      let storedQt : QTyp :=
        { etyp := ETyp.int
          poison := joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison)
          pred := storedPred }
      have hstored_pred_respects : PredRespectsTagMeaning tm storedPred := by
        intro k arg_name pred_body var_env hpred
        by_cases hp : res1.qualType.poison = true
        · simp [storedPred, hp] at hpred
        · have hpred_res2 :
            res2.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env := by
            simpa [storedPred, hp] using hpred
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
    · intro l hcontains
      have hcontains' : res.memEnv'.contains l = true := by
        simpa [ctxAfter] using hcontains
      have hsplit : res2.memEnv'.contains l = true ∨ l ∈ ls := by
        rw [hmem_res] at hcontains'
        exact assign_memEnv_formula_contains_eq_or_mem
          res2.memEnv' ls
          (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
          (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)
          l hcontains'
      cases hsplit with
      | inl hOld =>
          have hOldCtx : (ctxAfter ctx' res2).memEnv.contains l := by
            simpa [ctxAfter, ctx'] using hOld
          have hltOld' : l < (ctxAfter ctx' res2).nextLoc := hwf2 l hOldCtx
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
              (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)
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
              (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)
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
      constructor
      · have htag_res2_R2 : tagEnvConsistentWithRegime res2.tagEnv' res2.regime' := by
          simpa [ctxAfter, ctx'] using hregCtx2.1
        have htag_inv :
            tagEnvConsistentWithRegime (invalidateTagDeps res2.tagEnv' ls)
              (invalidateRegimeDeps res2.regime' res2.tagEnv' ls) :=
          tagEnvConsistentWithRegime_invalidateRegimeDeps res2.tagEnv' res2.regime' ls htag_res2_R2
        simpa [ctxAfter, htag_res, hRegime] using htag_inv
      · have hbound2 : res2.regime'.bound ≤ res2.nextTag' := by
          simpa [ctxAfter, ctx'] using hregCtx2.2
        have hbound_res2 : (invalidateRegimeDeps res2.regime' res2.tagEnv' ls).bound ≤ res2.nextTag' := by
          simpa [invalidateRegimeDeps] using hbound2
        simpa [ctxAfter, hRegime, hNextTag] using hbound_res2
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
                      pred := if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred }
              | _ =>
                  updateLocsetWeak res2.memEnv' ls
                    (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                    (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)).contains l = true := by
          simpa [hmem_res] using hcontains_res
        have hsplit : res2.memEnv'.contains l = true ∨ l ∈ ls := by
          exact assign_memEnv_formula_contains_eq_or_mem
            res2.memEnv' ls
            (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
            (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)
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
          exact hmono12.2.2 k hkR_res2
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
                      ioFree_guardClosure_pred_implies_tag_absent
                        (ctx := { ctxᵢ with
                          memEnv := res1.memEnv'
                          tagEnv := res1.tagEnv'
                          nextLoc := res1.nextLoc'
                          nextTag := res1.nextTag'
                          regime := res1.regime' })
                        (e := e2) (fuel := fuel') (res := res2)
                        (k := k') (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
                        htc2_expr hpred_res2
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
                              pred := if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred }
                      | _ =>
                          updateLocsetWeak res2.memEnv' ls
                            (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                            (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)).lookup l = some qt := by
                  simpa [hmem_res] using hlookup_res
                have hlookup_res2 : res2.memEnv'.lookup l = some qt := by
                  have hlookup_eq :
                      (match Std.ExtTreeSet.toList ls with
                        | [l0] =>
                            updateMemEnv res2.memEnv' l0
                              { etyp := ETyp.int
                                poison := joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison)
                                pred := if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred }
                        | _ =>
                            updateLocsetWeak res2.memEnv' ls
                              (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                              (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)).lookup l =
                        res2.memEnv'.lookup l :=
                    assign_memEnv_formula_lookup_eq_of_not_mem
                      res2.memEnv' ls
                      (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                      (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)
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
                      exact hmono12.2.2 k (by simp [hreg_res2])
                    cases hk0 : ctxᵢ.regime.lookup? k with
                    | none =>
                        exact (hk_ctxi_not_none hk0).elim
                    | some b0 =>
                        have hmono_keep : res2.regime'.lookup? k = some b0 ∨ res2.regime'.lookup? k = none :=
                          hmono12.2.1 k b0 hk0
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
                    ioFree_guardClosure_pred_implies_tag_absent
                      (ctx := { ctxᵢ with
                        memEnv := res1.memEnv'
                        tagEnv := res1.tagEnv'
                        nextLoc := res1.nextLoc'
                        nextTag := res1.nextTag'
                        regime := res1.regime' })
                      (e := e2) (fuel := fuel') (res := res2)
                      (k := k') (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
                      htc2_expr hpred_res2
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
            exact hmono12.2.2 k hkR_res2
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
            have heq₀w := LeanProofs.evalAtWorld_eq LeanProofs.defaultWorld hpure₀w
            have ht₀w : terminatesToW .ioFree LeanProofs.defaultWorld LeanProofs.defaultWorld (e1.assign e2)
                { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ := by
              exact ⟨fuel₀w, verbose₀w, by simpa [pure] using heq₀w⟩
            rcases ht₀w with ⟨fuel₀', verbose₀', heval₀'⟩
            have hvar_eq :=
                beval_preserves_varEnv .ioFree (e1.assign e2) fuel₀' verbose₀'
                { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀
                ⟨LeanProofs.defaultWorld, LeanProofs.defaultWorld, heval₀'⟩
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
                  hmono12.2.1 k b hreg
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
          exact hmono12.2.2 k hkR_res2
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
                      pred := if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred }
              | _ =>
                  updateLocsetWeak res2.memEnv' ls
                    (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                    (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)).contains l = true := by
          simpa [hmem_res] using hcontains_res
        have hsplit : res2.memEnv'.contains l = true ∨ l ∈ ls := by
          exact assign_memEnv_formula_contains_eq_or_mem
            res2.memEnv' ls
            (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
            (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)
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
                      ioFree_guardClosure_pred_implies_tag_absent
                        (ctx := { ctxᵢ with
                          memEnv := res1.memEnv'
                          tagEnv := res1.tagEnv'
                          nextLoc := res1.nextLoc'
                          nextTag := res1.nextTag'
                          regime := res1.regime' })
                        (e := e2) (fuel := fuel') (res := res2)
                        (k := k') (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
                        htc2_expr hpred_res2
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
                              pred := if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred }
                      | _ =>
                          updateLocsetWeak res2.memEnv' ls
                            (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                            (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)).lookup l = some qt := by
                  simpa [hmem_res] using hlookup_res
                have hlookup_res2 : res2.memEnv'.lookup l = some qt := by
                  have hlookup_eq :
                      (match Std.ExtTreeSet.toList ls with
                        | [l0] =>
                            updateMemEnv res2.memEnv' l0
                              { etyp := ETyp.int
                                poison := joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison)
                                pred := if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred }
                        | _ =>
                            updateLocsetWeak res2.memEnv' ls
                              (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                              (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)).lookup l =
                        res2.memEnv'.lookup l :=
                    assign_memEnv_formula_lookup_eq_of_not_mem
                      res2.memEnv' ls
                      (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                      (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)
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
                    ioFree_guardClosure_pred_implies_tag_absent
                      (ctx := { ctxᵢ with
                        memEnv := res1.memEnv'
                        tagEnv := res1.tagEnv'
                        nextLoc := res1.nextLoc'
                        nextTag := res1.nextTag'
                        regime := res1.regime' })
                      (e := e2) (fuel := fuel') (res := res2)
                      (k := k') (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
                      htc2_expr hpred_res2
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
            exact hmono12.2.2 k hkR_res2
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
            have heq₁w := LeanProofs.evalAtWorld_eq LeanProofs.defaultWorld hpure₁w
            have ht₁w : terminatesToW .ioFree LeanProofs.defaultWorld LeanProofs.defaultWorld (e1.assign e2)
                { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ := by
              exact ⟨fuel₁w, verbose₁w, by simpa [pure] using heq₁w⟩
            rcases ht₁w with ⟨fuel₁', verbose₁', heval₁'⟩
            have hvar_eq :=
                beval_preserves_varEnv .ioFree (e1.assign e2) fuel₁' verbose₁'
                { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁
                ⟨LeanProofs.defaultWorld, LeanProofs.defaultWorld, heval₁'⟩
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
                  hmono12.2.1 k b hreg
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
                      pred := if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred }
              | _ =>
                  updateLocsetWeak res2.memEnv' ls
                    (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                    (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)).contains l = true := by
          simpa [hmem_res] using hcontains_res
        exact
          assign_memEnv_formula_contains_eq_or_mem
            res2.memEnv' ls
            (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
            (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)
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
                      pred := if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred }
              | _ =>
                  updateLocsetWeak res2.memEnv' ls
                    (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                    (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)).lookup l = some qt := by
          simpa [hmem_res] using hlookup_res
        have hlookup_res2 : res2.memEnv'.lookup l = some qt := by
          have hlookup_eq :
              (match Std.ExtTreeSet.toList ls with
                | [l0] =>
                    updateMemEnv res2.memEnv' l0
                      { etyp := ETyp.int
                        poison := joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison)
                        pred := if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred }
                | _ =>
                    updateLocsetWeak res2.memEnv' ls
                      (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                      (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)).lookup l =
                  res2.memEnv'.lookup l :=
            assign_memEnv_formula_lookup_eq_of_not_mem
              res2.memEnv' ls
              (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
              (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)
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
          simpa [ctxAfter, ctx'] using hregCtx2.1
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
                          pred := if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred }
                  | _ =>
                      updateLocsetWeak res2.memEnv' ls
                        (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                        (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)).lookup l = some qt := by
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
                            pred := if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred }).lookup l =
                          some qt := by
                      simpa [hls] using hlookup_formula
                    have hqtEq :
                        qt =
                          { etyp := ETyp.int
                            poison := joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison)
                            pred := if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred } := by
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
                                    pred := if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred } =
                                  some k := by
                              simpa [hqtEq] using htag
                            cases hp : res1.qualType.poison with
                            | false =>
                                simpa [qtypGuardTag, hp] using htag_stored
                            | true =>
                                simp [qtypGuardTag, hp] at htag_stored
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
                                    (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)).lookup l =
                                    some qt := by
                                simpa [hls] using hlookup_formula
                              unfold updateLocsetWeak at hlookup_weak
                              set joined :=
                                LocSet.fold ls
                                  (joinPoison ctxᵢ.pc
                                    (joinPoison res1.qualType.poison res2.qualType.poison),
                                    if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)
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
                                        if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)).1) =
                                    false := by
                                unfold joined at hjoined_false
                                unfold LocSet.fold at hjoined_false
                                rw [Std.ExtTreeSet.foldl_eq_foldl_toList] at hjoined_false
                                exact hjoined_false
                              have hpoison_old : qtOld.poison = false :=
                                list_fold_joinPoison_false_implies_lookup_poison_false
                                  res2.memEnv' ls.toList
                                  (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                                  (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)
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
                                      (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)).lookup l =
                                      some qt := by
                                  simpa [hls] using hlookup_formula
                                unfold updateLocsetWeak at hlookup_weak
                                set joined :=
                                  LocSet.fold ls
                                    (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison),
                                      if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)
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
                                          if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)).1) = false := by
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
                                                if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)).1) = true := by
                                        simpa [hbase] using
                                          list_fold_joinPoison_first_true
                                            res2.memEnv' ls.toList
                                            (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)
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
                                ioFree_guardClosure_pred_implies_tag_absent
                                  (ctx := { ctxᵢ with
                                    memEnv := res1.memEnv'
                                    tagEnv := res1.tagEnv'
                                    nextLoc := res1.nextLoc'
                                    nextTag := res1.nextTag'
                                    regime := res1.regime' })
                                  (e := e2) (fuel := fuel') (res := res2)
                                  (k := k') (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
                                  htc2_expr hpred_res2
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
                                      (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)).lookup
                                    l = some qt := by
                                  simpa [hls] using hlookup_formula
                                unfold updateLocsetWeak at hlookup_weak
                                set joined :=
                                  LocSet.fold ls
                                    (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison),
                                      if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)
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
                                          if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)).2) =
                                      Predicate.guardOnly k' := by
                                  unfold joined at hjoined_pred
                                  unfold LocSet.fold at hjoined_pred
                                  rw [Std.ExtTreeSet.foldl_eq_foldl_toList] at hjoined_pred
                                  exact hjoined_pred
                                have htag_init_and_all :=
                                  list_fold_joinPredicates_guardOnly_implies_init_and_lookup_guardTag
                                    res2.memEnv' ls.toList
                                    (joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison))
                                    (if res1.qualType.poison = true then Predicate.noPred else res2.qualType.pred)
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
                                    simpa [hres1_poison] using htag_stored
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
  refine ⟨θ₀2, θ₁2, hθext₀, hθext₁, ?_, ?_, hTm_final, hwf_final, hwfcf₀_final, hwfcf₁_final, hric₀_final, hric₁_final, hreg_final, hcwr₀_final, hcwr₁_final, hagree_final, ?_, ?_, ?_⟩
  · subst ho₀
    simpa [hEtyp] using valueHasETyp.unit (θ := θ₀2)
  · subst ho₁
    simpa [hEtyp] using valueHasETyp.unit (θ := θ₁2)
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
