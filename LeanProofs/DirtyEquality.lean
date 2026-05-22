import LeanProofs.FaultRobustness

/-!
# Dirty Critical-Input Agreement

This file isolates the over-constraint described in `doc/dirty-equality-question.md`:
under the current top-level critical-input agreement premise, a bound first-order
dirty critical input with a false guard regime cannot satisfy critical agreement.
-/

open Std

lemma no_agreeValueUnder_dirty_guard_false_int
    {predSat : PredSat} {R : Regime} {μ₁ μ₂ : Memory}
    {θ₁ θ₂ : RealizationMap} {qt : QTyp} {v₁ v₂ : Value} {k : Tag}
    (hpoison : qt.poison = true)
    (hetyp : qt.etyp = ETyp.int)
    (htag : qtypGuardTag qt = some k)
    (hR : R.lookup? k = some false) :
    ¬ agreeValueUnder predSat R μ₁ μ₂ θ₁ θ₂ qt v₁ v₂ := by
  intro hagree
  cases hagree with
  | clean_eq_nonref_nonarrow hpoison_false _ _ _ =>
      simp [hpoison] at hpoison_false
  | clean_internal_arrow _ hetyp_arrow _ _ _ _ _ _ _ _ _ =>
      rw [hetyp] at hetyp_arrow
      cases hetyp_arrow
  | dirty_internal_arrow _ hisArrow _ _ =>
      rw [hetyp] at hisArrow
      simp [ETyp.isArrow] at hisArrow
  | clean_internal_parrow _ hetyp_parrow _ _ _ _ _ _ _ _ _ =>
      rw [hetyp] at hetyp_parrow
      cases hetyp_parrow
  | dirty_internal_parrow _ hisParrow _ _ =>
      rw [hetyp] at hisParrow
      simp [ETyp.isParrow] at hisParrow
  | clean_ref hpoison_false _ _ _ _ _ _ =>
      simp [hpoison] at hpoison_false
  | withPred_true_eq k' htag' hR' _ _ _ =>
      have hk : k = k' := by
        rw [htag] at htag'
        exact Option.some.inj htag'
      subst k'
      rw [hR] at hR'
      cases hR'
  | withPred_true_ref k' htag' hR' _ _ _ _ _ _ =>
      have hk : k = k' := by
        rw [htag] at htag'
        exact Option.some.inj htag'
      subst k'
      rw [hR] at hR'
      cases hR'

lemma no_agreeVarUnder_dirty_guard_false_int
    {predSat : PredSat} {R : Regime} {μ₁ μ₂ : Memory} {ρ₁ ρ₂ : VarEnv}
    {θ₁ θ₂ : RealizationMap} {x : Name} {qt : QTyp} {v₁ v₂ : Value} {k : Tag}
    (hpoison : qt.poison = true)
    (hetyp : qt.etyp = ETyp.int)
    (htag : qtypGuardTag qt = some k)
    (hR : R.lookup? k = some false)
    (hlookup₁ : ρ₁.lookup x = some v₁)
    (_hlookup₂ : ρ₂.lookup x = some v₂) :
    ¬ agreeVarUnder predSat R μ₁ ρ₁ μ₂ ρ₂ θ₁ θ₂ (x, qt) := by
  intro hagree
  cases hagree with
  | agree_values _ _ _ _ _ _ hagree_value =>
      exact no_agreeValueUnder_dirty_guard_false_int hpoison hetyp htag hR hagree_value
  | both_none _ _ hnone₁ hnone₂ =>
      rw [hlookup₁] at hnone₁
      cases hnone₁

lemma no_agreeOnCriticalInputs_dirty_guard_false_int_var
    {predSat : PredSat} {R : Regime} {s : InputSpec}
    {μ₁ μ₂ : Memory} {ρ₁ ρ₂ : VarEnv} {θ₁ θ₂ : RealizationMap}
    {x : Name} {qt : QTyp} {v₁ v₂ : Value} {k : Tag}
    (hmem : (x, qt) ∈ s.vars.toList)
    (hpoison : qt.poison = true)
    (hetyp : qt.etyp = ETyp.int)
    (htag : qtypGuardTag qt = some k)
    (hR : R.lookup? k = some false)
    (hlookup₁ : ρ₁.lookup x = some v₁)
    (hlookup₂ : ρ₂.lookup x = some v₂) :
    ¬ agreeOnCriticalInputsUnderRegimeSpec predSat R s μ₁ ρ₁ θ₁ μ₂ ρ₂ θ₂ := by
  intro hagree
  rcases hagree with ⟨_, hagree_vars⟩
  rw [List.forall_iff_forall_mem] at hagree_vars
  exact
    no_agreeVarUnder_dirty_guard_false_int
      hpoison hetyp htag hR hlookup₁ hlookup₂ (hagree_vars (x, qt) hmem)

lemma no_agreeOnCriticalInputs_dirty_guard_false_int_var_of_runtime
    {predSat : PredSat} {R : Regime} {s : InputSpec} {ctx : TypeContext}
    {μ₁ μ₂ : Memory} {ρ₁ ρ₂ : VarEnv} {θ₁ θ₂ : RealizationMap}
    {x : Name} {qt : QTyp} {k : Tag}
    (hlookup_s : s.vars.lookup x = some qt)
    (hctx : ctxMatchesInputSpec s ctx)
    (hric₁ : runtimeInstantiatesCtx ctx μ₁ ρ₁ θ₁)
    (hric₂ : runtimeInstantiatesCtx ctx μ₂ ρ₂ θ₂)
    (hpoison : qt.poison = true)
    (hetyp : qt.etyp = ETyp.int)
    (htag : qtypGuardTag qt = some k)
    (hR : R.lookup? k = some false) :
    ¬ agreeOnCriticalInputsUnderRegimeSpec predSat R s μ₁ ρ₁ θ₁ μ₂ ρ₂ θ₂ := by
  intro hagree
  rcases hctx with ⟨_, hctx_vars, _, _⟩
  have hctx_lookup : ctx.varEnv.lookup x = some qt := hctx_vars hlookup_s
  rcases hric₁.2 hctx_lookup with ⟨v₁, hlookup₁, _⟩
  rcases hric₂.2 hctx_lookup with ⟨v₂, hlookup₂, _⟩
  have hmem : (x, qt) ∈ s.vars.toList := by
    rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some]
    dsimp [VarTypeEnv.lookup] at hlookup_s
    simpa using hlookup_s
  exact
    no_agreeOnCriticalInputs_dirty_guard_false_int_var
      hmem hpoison hetyp htag hR hlookup₁ hlookup₂ hagree

theorem FaultRobustnessSpec_vacuous_of_dirty_guard_false_int_var
    (e : Expr) (s : InputSpec) (obs : ObservableSpec) (ctx : TypeContext)
    (predSat : PredSat) (tm : TagMeaning)
    {x : Name} {qt : QTyp} {k : Tag}
    (hlookup_s : s.vars.lookup x = some qt)
    (hctx : ctxMatchesInputSpec s ctx)
    (hpoison : qt.poison = true)
    (hetyp : qt.etyp = ETyp.int)
    (htag : qtypGuardTag qt = some k)
    (hR : ctx.regime.lookup? k = some false) :
    FaultRobustnessSpec e s obs ctx predSat tm := by
  intro mode μ₁ μ₂ ρ₁ ρ₂ θ₁ θ₂ a₁ a₂ pm cf₁ cf₂ o₁ o₂ _hwfRegime _hθ₁ _hθ₂
    _hwfcfg₁ _hwfcfg₂ _hics₁ _hics₂ hric₁ hric₂ _htrusted₁ _htrusted₂ _hcrs₁
    _hcrs₂ hagree _htrusted _ht₁ _ht₂
  exact False.elim
    (no_agreeOnCriticalInputs_dirty_guard_false_int_var_of_runtime
      hlookup_s hctx hric₁ hric₂ hpoison hetyp htag hR hagree)
