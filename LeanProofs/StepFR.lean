/-
  StepFR.lean - Shared definitions and utility lemmas for fault-robustness proofs.

  Core definitions (StepFR, resultAgreesIfClean, tagEnvConsistentWithRegime, etc.)
  and helper lemmas used by multiple stepFR_* case proofs.
-/
import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.BigStep
import Mathlib.Data.List.Forall2

import LeanProofs.FaultRobustness
import LeanProofs.TypeSafety
import LeanProofs.Aux
import LeanProofs.SemanticsProperties
import LeanProofs.IOHelpers
import LeanProofs.Equality
import LeanProofs.RegimeConsistency
import LeanProofs.VarEnvPreservation
import LeanProofs.MemoryMonotonicity
import Std.Data.ExtTreeMap.Lemmas
import Std.Data.ExtTreeSet.Lemmas

open List
open List.Mem
open Std
open scoped MemoryTypeEnv

def resultAgreesIfClean (predSat : PredSat) (R : Regime) (μ₀ μ₁ : Memory)
  (θ₀ θ₁ : RealizationMap) (qt : QTyp) (o₀ o₁ : Value) : Prop :=
  qtypCleanUnder R qt →
    agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁

-- When qt.poison = true and qt.pred = noPred, qtypCleanUnder is impossible,
-- so resultAgreesIfClean is vacuously true.
lemma resultAgreesIfClean_of_poison_noPred
    {predSat : PredSat} {R : Regime} {μ₀ μ₁ : Memory}
    {θ₀ θ₁ : RealizationMap} {qt : QTyp} {o₀ o₁ : Value}
    (hp : qt.poison = true) (hpred : qt.pred = Predicate.noPred) :
    resultAgreesIfClean predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ := by
  intro hcu
  cases hcu with
  | clean hpoison => simp [hp] at hpoison
  | guard k htag _ _ => simp [qtypGuardTag, hpred] at htag

-- Tag-environment consistency for a regime: tags known true in the typing
-- context must be true in the regime interpretation.
def tagEnvConsistentWithRegime (tagEnv : TagEnv) (regime : Regime) : Prop :=
  ∀ k deps, tagEnv.get? k = some ⟨true, deps⟩ → regime.lookup? k = some true

-- Regime consistency with a typing context: (i) tags known true in the context must be true in the
-- regime interpretation, and (ii) the regime's bound is below the context's fresh-tag supply.
--
-- Intended reading: the context's regime only interprets *input/spec* tags (< regime.bound). The
-- context's `nextTag` tracks the current supply for fresh internal tags, and it should stay above
-- `regime.bound`.
def regimeConsistentWithCtx (ctx : TypeContext) : Prop :=
  tagEnvConsistentWithRegime ctx.tagEnv ctx.regime ∧ ctx.regime.bound ≤ ctx.nextTag

-- ------------------------
-- TagEnv/Regime consistency preservation lemmas
--
-- These are proof-only facts about the typechecker infrastructure:
--   * `tagEnvConsistentWithRegime` is stable under the TagEnv operations used by typing
--     (insertion, invalidation, joins), and
--   * typechecking preserves the invariant when starting from a consistent context.

lemma tagEnvConsistentWithRegime_insert_true
    (tagEnv : TagEnv) (R : Regime) (k : Tag) (deps : Deps)
    (h : tagEnvConsistentWithRegime tagEnv R)
    (hk : R.lookup? k = some true) :
    tagEnvConsistentWithRegime (tagEnv.insert k ⟨true, deps⟩) R := by
  intro k' deps' hget
  by_cases hkk' : k' = k
  · subst hkk'
    -- The inserted binding is the only way to obtain `k ↦ true`.
    simpa [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert_self] using hk
  · -- Otherwise, defer to the old environment.
    have hcmp : compare k k' ≠ Ordering.eq := by
      -- For Nat tags, `compare k k' = .eq` iff `k = k'`.
      intro hce
      have : k = k' := (Nat.compare_eq_eq).1 hce
      exact hkk' this.symm
    have hget' : tagEnv.get? k' = some ⟨true, deps'⟩ := by
      -- `insert` at a different key does not affect lookups.
      simp [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert, hcmp] at hget
      exact hget
    exact h k' deps' hget'

lemma tagEnvConsistentWithRegime_insert_false
    (tagEnv : TagEnv) (R : Regime) (k : Tag) (deps : Deps)
    (h : tagEnvConsistentWithRegime tagEnv R) :
    tagEnvConsistentWithRegime (tagEnv.insert k ⟨false, deps⟩) R := by
  intro k' deps' hget
  by_cases hkk' : k' = k
  · subst hkk'
    -- Impossible: the inserted value is `false`.
    simp [Std.ExtTreeMap.get?_eq_getElem?] at hget
  · have hcmp : compare k k' ≠ Ordering.eq := by
      intro hce
      have : k = k' := (Nat.compare_eq_eq).1 hce
      exact hkk' this.symm
    have hget' : tagEnv.get? k' = some ⟨true, deps'⟩ := by
      simp [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert, hcmp] at hget
      exact hget
    exact h k' deps' hget'

-- `invalidateTagDeps` only removes entries; it never creates new `true` bindings.
lemma tagEnvConsistentWithRegime_invalidate
    (tagEnv : TagEnv) (R : Regime) (ls : LocSet)
    (h : tagEnvConsistentWithRegime tagEnv R) :
    tagEnvConsistentWithRegime (invalidateTagDeps tagEnv ls) R := by
  intro k deps hget
  -- Filtering can only keep an existing binding.
  have hget' : tagEnv.get? k = some ⟨true, deps⟩ := by
    -- `invalidateTagDeps` is `filter`; use the filter lookup lemma.
    unfold invalidateTagDeps at hget
    -- Apply filter lemma: `(t.filter f)[k]? = Option.filter (f k) t[k]?`
    rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_filter'] at hget
    -- Case split on the original value at k
    cases h0 : tagEnv.get? k
    · -- If tagEnv[k] = none, then filter returns none, contradicting hget
      rw [← Std.ExtTreeMap.get?_eq_getElem?, h0] at hget
      simp at hget
    · -- If tagEnv[k] = some val, and filter returns some, then val is preserved
      rw [← Std.ExtTreeMap.get?_eq_getElem?, h0] at hget
      simp at hget
      rw [hget.1]
  exact h k deps hget'

-- `invalidateRegimeDeps` keeps the regime and tag environment in sync: if a tag survives
-- invalidation in the TagEnv, it also survives in the regime map.
lemma invalidateRegimeDeps_preserves_true
    (tagEnv : TagEnv) (R : Regime) (ls : LocSet)
    (h : tagEnvConsistentWithRegime tagEnv R) :
    tagEnvConsistentWithRegime (invalidateTagDeps tagEnv ls) (invalidateRegimeDeps R tagEnv ls) := by
  intro k deps hget
  -- From TagEnv consistency, the *pre* regime maps `k ↦ true`.
  have hkR : R.lookup? k = some true := by
    -- `invalidateTagDeps` only removes entries; recover the original binding.
    have hkeep : tagEnv.get? k = some ⟨true, deps⟩ := by
      unfold invalidateTagDeps at hget
      rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_filter'] at hget
      cases h0 : tagEnv.get? k
      · -- If tagEnv[k] = none, then filter returns none, contradicting hget
        rw [← Std.ExtTreeMap.get?_eq_getElem?, h0] at hget
        simp at hget
      · -- If tagEnv[k] = some val, and filter returns some, then val is preserved
        rw [← Std.ExtTreeMap.get?_eq_getElem?, h0] at hget
        simp at hget
        rw [hget.1]
    exact h k deps hkeep
  -- Now show the invalidated regime still maps `k ↦ true`.
  unfold invalidateRegimeDeps
  -- `lookup?` additionally checks the bound.
  -- Use the fact `hkR` provides: `k < R.bound` and `R.map.get? k = some true`.
  dsimp [Regime.lookup?] at hkR
  split_ifs at hkR with hklt
  · -- k < R.bound
    -- We need to show the filtered map still has `k ↦ true`.
    dsimp only [invalidateTagDeps]
    -- First, `invalidated.contains k = true` since `invalidateTagDeps` kept `k`.
    have hcontains : (invalidateTagDeps tagEnv ls).contains k = true := by
      -- `contains` checks if `get?` returns `some`
      simp only [Std.ExtTreeMap.contains_eq_isSome_getElem?]
      rw [← Std.ExtTreeMap.get?_eq_getElem?, hget]
      rfl
    -- Use `getElem?_filter'` for the map filter.
    have hmap : (R.map.filter (fun k _ => (invalidateTagDeps tagEnv ls).contains k)).get? k = some true := by
      -- Filter keeps `k` because `hcontains` is true.
      -- `get?` on the filtered map is `Option.filter` on the original get?.
      simp [Std.ExtTreeMap.get?_eq_getElem?, hcontains, hkR]
    -- Finally, discharge the `lookup?` of the new regime.
    simp [Regime.lookup?, hklt]
    constructor
    · -- Show R.map[k]? = some true
      exact hkR
    · -- Show k is in the filtered tag env (i.e., k is in invalidateTagDeps)
      unfold invalidateTagDeps at hget
      -- Membership in ExtTreeMap means get? returns some
      show (ExtTreeMap.filter (fun x tv => !tv.deps.any (ExtTreeSet.contains ls)) tagEnv).contains k = true
      simp only [Std.ExtTreeMap.contains_eq_isSome_getElem?]
      rw [← Std.ExtTreeMap.get?_eq_getElem?, hget]
      rfl

-- Join of TagEnvs/Regimes preserves the invariant (meet-style join: only agreed tags remain).
lemma tagEnvConsistentWithRegime_join
    (tagEnv₁ tagEnv₂ : TagEnv) (R₁ R₂ : Regime)
    (h₁ : tagEnvConsistentWithRegime tagEnv₁ R₁)
    (h₂ : tagEnvConsistentWithRegime tagEnv₂ R₂) :
    tagEnvConsistentWithRegime (joinTagEnvs tagEnv₁ tagEnv₂) (joinRegimes R₁ R₂) := by
  intro k deps hget
  -- Use helper lemma to extract that both inputs must have compatible entries
  have hgetTag : (joinTagEnvs tagEnv₁ tagEnv₂).get? k = some ⟨true, deps⟩ := hget
  unfold joinTagEnvs at hgetTag
  -- Determine if k is in the combined keys
  let f : Tag → Option TagVal → Option TagVal → Option TagVal := fun _ otv1 otv2 =>
    match otv1, otv2 with
    | some ⟨b1, deps1⟩, some ⟨b2, deps2⟩ => if b1 == b2 then some ⟨b1, LocSet.union deps1 deps2⟩ else none
    | some _, none => none
    | none, some _ => none
    | none, none => none
  have hcombine : (combineExtTreeMaps tagEnv₁ tagEnv₂ f).get? k = some ⟨true, deps⟩ := hgetTag
  simp only [combineExtTreeMaps] at hcombine
  -- k must be in the key list for the result to be some
  have hk_mem : k ∈ (tagEnv₁.keys ++ tagEnv₂.keys).eraseDups := by
    by_contra hnot
    have := combineExtTreeMaps_go_get_not_mem tagEnv₁ tagEnv₂ f
            (tagEnv₁.keys ++ tagEnv₂.keys).eraseDups ({} : TagEnv) k hnot
    simp [this] at hcombine
  -- Use the mem lemma to get the join function result
  have hgo := combineExtTreeMaps_go_get_mem tagEnv₁ tagEnv₂ f
              (tagEnv₁.keys ++ tagEnv₂.keys).eraseDups ({} : TagEnv) k hk_mem
  simp only [Std.ExtTreeMap.get?_eq_getElem?] at hcombine hgo
  rw [hcombine] at hgo
  -- Analyze what f k must return - need to simplify hgo to extract the constraint
  simp only [f] at hgo
  -- Do case analysis on both get? results
  cases h1 : tagEnv₁.get? k <;> cases h2 : tagEnv₂.get? k
  · -- both none - contradiction with hgo
    simp [← Std.ExtTreeMap.get?_eq_getElem?, h1, h2] at hgo
  · -- tagEnv₁ none, tagEnv₂ some - contradiction
    simp [← Std.ExtTreeMap.get?_eq_getElem?, h1, h2] at hgo
  · -- tagEnv₁ some, tagEnv₂ none - contradiction
    simp [← Std.ExtTreeMap.get?_eq_getElem?, h1, h2] at hgo
  · -- both some - this is the only valid case
    rename_i val1 val2
    rcases val1 with ⟨b1, deps1⟩
    rcases val2 with ⟨b2, deps2⟩
    simp [← Std.ExtTreeMap.get?_eq_getElem?, h1, h2] at hgo
    split_ifs at hgo with heq
    · -- Case: b1 == b2
      have heq' : b1 = b2 := by
        cases b1 <;> cases b2 <;> simp at heq <;> trivial
      simp at hgo
      -- hgo: b1 = true ∧ deps = deps1.union deps2
      have hb1 := hgo.1
      subst hb1 heq'
      -- Use the premises to get `R₁.lookup? k = some true` and `R₂.lookup? k = some true`.
      have hkR1 : R₁.lookup? k = some true := h₁ k deps1 h1
      have hkR2 : R₂.lookup? k = some true := h₂ k deps2 h2
      -- Now compute `joinRegimes R₁ R₂`.lookup? k.
      unfold joinRegimes
      -- `lookup?` requires `k < min bound`; this follows from `hkR1`/`hkR2`.
      -- Extract the bound checks from the lookup definitions.
      have hklt1 : k < R₁.bound := by
        -- `lookup?` is `if k < bound then ... else none`.
        dsimp [Regime.lookup?] at hkR1
        split_ifs at hkR1 with hklt; try cases hkR1
        exact hklt
      have hklt2 : k < R₂.bound := by
        dsimp [Regime.lookup?] at hkR2
        split_ifs at hkR2 with hklt; try cases hkR2
        exact hklt
      have hklt : k < min R₁.bound R₂.bound := Nat.lt_min.2 ⟨hklt1, hklt2⟩
      -- Also extract the underlying map lookups.
      have hkmap1 : R₁.map.get? k = some true := by
        dsimp [Regime.lookup?] at hkR1
        split_ifs at hkR1
        · exact hkR1
      have hkmap2 : R₂.map.get? k = some true := by
        dsimp [Regime.lookup?] at hkR2
        split_ifs at hkR2
        · exact hkR2
      -- Show the joined map contains `k ↦ true`.
      -- Use the same approach as for TagEnv
      have hkjoined : (combineExtTreeMaps R₁.map R₂.map (fun _ ob1 ob2 =>
        match ob1, ob2 with
        | some b1, some b2 => if b1 == b2 then some b1 else none
        | _, _ => none)).get? k = some true := by
        simp only [combineExtTreeMaps]
        have hk_mem_regime : k ∈ (R₁.map.keys ++ R₂.map.keys).eraseDups := by
          have hk_contains : R₁.map.contains k := by
            rw [Std.ExtTreeMap.contains_eq_isSome_getElem?, ← Std.ExtTreeMap.get?_eq_getElem?, hkmap1]
            rfl
          have hk_in_keys : k ∈ R₁.map.keys := ExtTreeMap.mem_keys.2 hk_contains
          have hmem_append : k ∈ R₁.map.keys ++ R₂.map.keys := List.mem_append_left R₂.map.keys hk_in_keys
          exact List.mem_eraseDups_of_mem hmem_append
        have hgo_regime := combineExtTreeMaps_go_get_mem R₁.map R₂.map
                           (fun _ ob1 ob2 => match ob1, ob2 with
                             | some b1, some b2 => if b1 == b2 then some b1 else none
                             | _, _ => none)
                           (R₁.map.keys ++ R₂.map.keys).eraseDups ({} : ExtTreeMap Tag Bool) k hk_mem_regime
        -- hgo_regime: (combineExtTreeMaps.go ...)[k]? = match f k (R₁.map[k]?) (R₂.map[k]?) with ...
        -- We know R₁.map.get? k = some true and R₂.map.get? k = some true
        -- So f k (some true) (some true) = if (true == true) then some true else none = some true
        simp only [← Std.ExtTreeMap.get?_eq_getElem?, hkmap1, hkmap2] at hgo_regime
        -- Now the match simplifies: true == true = true, so we get some true
        simp only [beq_self_eq_true, ↓reduceIte] at hgo_regime
        -- Convert .get? to [k]? in the goal and use hgo_regime
        rw [Std.ExtTreeMap.get?_eq_getElem?]
        exact hgo_regime
      -- Finish the lookup.
      simp only [Regime.lookup?, hklt, ↓reduceIte, Std.ExtTreeMap.get?_eq_getElem?]
      rw [← Std.ExtTreeMap.get?_eq_getElem?]
      exact hkjoined


-- Helper lemma: regimeBounded transfers under monotonicity (bounds are equal)
lemma regimeBounded_of_monotoneStep (R R' : Regime)
    (h_bounded : regimeBounded R)
    (h_mono : Regime.monotoneStep R R') :
    regimeBounded R' := by
  intro k hk
  have hbound_eq : R'.bound = R.bound := h_mono.1
  rw [hbound_eq] at hk
  have hR_none := h_bounded k hk
  -- Use contrapositive of h_mono.2.2: R.lookup? k = none → R'.lookup? k = none
  by_contra h_not_none
  have h_R_not_none := h_mono.2.2 k h_not_none
  exact h_R_not_none hR_none

-- Bridge lemma: connect spec-indexed consistency to context-indexed consistency
lemma consistentRegimeSpec_implies_consistentWithRegime
    (predSat : PredSat) (R : Regime) (s : InputSpec) (ctx : TypeContext)
    (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
    (h_spec : consistentRegimeSpec predSat R s μ ρ θ)
    (h_ric : runtimeInstantiatesCtx ctx μ ρ θ)
    (h_trusted_init : trustedVarsClosureRegimeInit predSat R s ctx μ ρ θ)
    (h_input_wf : wfInputSpec s)
    (h_match : ctxMatchesInputSpec s ctx)
    (h_wf : wfRegime R s)
    (_h_bounded : regimeBounded R) :
    consistentWithRegime predSat R ctx μ ρ θ := by
  rcases h_match with ⟨hctx_mem, hctx_vars, hctx_mem_hyg, hctx_vars_hyg_deep⟩
  rcases h_trusted_init with ⟨htrusted_init⟩
  rcases h_input_wf with ⟨_hInputMem, _hInputVarsDeep, hInputVarsFirstOrder⟩
  have hctx_vars_hyg :
      ∀ x qt k, ctx.varEnv.lookup x = some qt → qtypGuardTag qt = some k →
        ¬ s.vars.hasKey x → k ∉ inputSpecTags s := by
    exact
      (deep_implies_shallow (P := fun env =>
        ∀ x qt k, env.lookup x = some qt → qtypGuardTag qt = some k →
          ¬ s.vars.hasKey x → k ∉ inputSpecTags s) (env := ctx.varEnv) hctx_vars_hyg_deep)
  simp only [consistentWithRegime]
  constructor
  · intro l qt k hlookup hguard hRdef
    -- From wfRegime: any tag interpreted by R must be a spec tag.
    have hk_in_tags : k ∈ inputSpecTags s := by
      have h_isSome : (R.lookup? k).isSome := by
        cases h : R.lookup? k with
        | none => exact False.elim (hRdef h)
        | some _b => simp
      exact h_wf.2.2 k h_isSome
    -- Tag hygiene in ctx forbids non-spec entries from reusing spec tags, so l must be a spec key.
    have hkey : s.locs.hasKey l := by
      by_contra hnot
      have : k ∉ inputSpecTags s := hctx_mem_hyg l qt k hlookup hguard hnot
      exact this hk_in_tags
    -- Recover the spec-qualified type at l and use the spec-indexed regime consistency.
    have hcontains : s.locs.contains l = true := by
      simpa [MemoryTypeEnv.hasKey] using hkey
    have hmem : l ∈ s.locs :=
      (Std.ExtTreeMap.contains_iff_mem).1 hcontains
    have hlookup_isSome : (s.locs[l]?).isSome = true :=
      (Std.ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
    cases hlookup_s : s.locs[l]? with
    | none =>
        simp [hlookup_s] at hlookup_isSome
    | some e_s =>
        let qt_s : QTyp := ⟨ETyp.int, e_s.poison, e_s.pred⟩
        have hlookup_s' : s.locs.lookup l = some qt_s := by
          simp only [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?, hlookup_s, Option.map]; rfl
        have hctx_lookup' : ctx.memEnv.lookup l = some qt_s := hctx_mem hlookup_s'
        have hqt : qt_s = qt := by
          have : some qt_s = some qt := by
            calc
              some qt_s = ctx.memEnv.lookup l := by
                symm
                exact hctx_lookup'
              _ = some qt := by
                exact hlookup
          exact Option.some.inj this
        have h_locs_forall := h_spec.1
        rw [List.forall_iff_forall_mem] at h_locs_forall
        have hmem' : (l, qt_s) ∈ memEnvToLocQTypList s.locs := by
          rw [memEnvToLocQTypList, List.mem_map]
          refine ⟨(l, e_s), (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some).2 hlookup_s, ?_⟩
          rfl
        have h_loc_regime : locsRegime predSat R μ θ (l, qt_s) :=
          h_locs_forall (l, qt_s) hmem'
        simpa [hqt] using h_loc_regime
  constructor
  · intro x qt k hlookup hguard hRdef
    have hk_in_tags : k ∈ inputSpecTags s := by
      have h_isSome : (R.lookup? k).isSome := by
        cases h : R.lookup? k with
        | none => exact False.elim (hRdef h)
        | some _b => simp
      exact h_wf.2.2 k h_isSome
    have hkey : s.vars.hasKey x := by
      by_contra hnot
      have : k ∉ inputSpecTags s := hctx_vars_hyg x qt k hlookup hguard hnot
      exact this hk_in_tags
    have hcontains : s.vars.contains x = true := by
      simpa [VarTypeEnv.hasKey] using hkey
    have hmem : x ∈ s.vars :=
      (Std.ExtTreeMap.contains_iff_mem).1 hcontains
    have hlookup_isSome : (s.vars[x]?).isSome = true :=
      (Std.ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
    cases hlookup_s : s.vars[x]? with
    | none =>
        simp [hlookup_s] at hlookup_isSome
    | some qt_s =>
        have hlookup_s' : s.vars.lookup x = some qt_s := by
          simpa [VarTypeEnv.lookup] using hlookup_s
        have hctx_lookup' : ctx.varEnv.lookup x = some qt_s := hctx_vars hlookup_s'
        have hqt : qt_s = qt := by
          have : some qt_s = some qt := by
            calc
              some qt_s = ctx.varEnv.lookup x := by
                symm
                exact hctx_lookup'
              _ = some qt := by
                exact hlookup
          exact Option.some.inj this
        have h_vars_forall := h_spec.2
        rw [List.forall_iff_forall_mem] at h_vars_forall
        have hmem' : (x, qt_s) ∈ s.vars.toList := by
          rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some]
          dsimp [VarTypeEnv.lookup] at hlookup_s'
          simpa using hlookup_s'
        have h_var_regime : varsRegime predSat R μ ρ (x, qt_s) :=
          h_vars_forall (x, qt_s) hmem'
        simpa [hqt] using h_var_regime
  · -- Third conjunct: closureCapturedVarsRegime for all variable-value pairs.
    intro x qt v hlookup hlookup_v
    by_cases hkey : s.vars.hasKey x
    · -- Critical input variable: `wfInputSpec` now restricts `s.vars` to first-order types,
      -- so closureCapturedVarsRegime follows from runtime typing via the non-closure case.
      have hcontains : s.vars.contains x = true := by
        simpa [VarTypeEnv.hasKey] using hkey
      have hmem : x ∈ s.vars :=
        (Std.ExtTreeMap.contains_iff_mem).1 hcontains
      have hlookup_isSome : (s.vars[x]?).isSome = true :=
        (Std.ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
      cases hlookup_s : s.vars[x]? with
      | none =>
          simp [hlookup_s] at hlookup_isSome
      | some qt_s =>
          have hlookup_s' : s.vars.lookup x = some qt_s := by
            simpa [VarTypeEnv.lookup] using hlookup_s
          have hctx_lookup' : ctx.varEnv.lookup x = some qt_s := hctx_vars hlookup_s'
          have hqt : qt_s = qt := by
            have : some qt_s = some qt := by
              calc
                some qt_s = ctx.varEnv.lookup x := by
                  symm
                  exact hctx_lookup'
                _ = some qt := by
                  exact hlookup
            exact Option.some.inj this
          have hnon_s : nonClosureQTyp qt_s := hInputVarsFirstOrder x qt_s hlookup_s'
          have hnon : nonClosureQTyp qt := by simpa [hqt] using hnon_s
          rcases h_ric.2 hlookup with ⟨v', hlookup_v', hvet⟩
          have hv' : v' = v := by
            have : (some v' : Option Value) = some v := by
              rw [← hlookup_v', hlookup_v]
            exact Option.some.inj this
          subst hv'
          have hnotfun : qt.etyp.isFunctionType = false := by
            cases qt with
            | mk etyp p pred =>
                cases etyp <;>
                  simp [nonClosureQTyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hnon ⊢
          refine closureCapturedVarsRegime.intro ?_
          refine deepValueQTypProperty.nonClosure ?_ ?_
          · intro xp bd rc hval
            subst hval
            generalize het : qt.etyp = et at hvet hnotfun
            cases hvet with
            | closure =>
                simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hnotfun
          · intro xp bd rc hval
            subst hval
            generalize het : qt.etyp = et at hvet hnotfun
            cases hvet with
            | peClosure =>
                simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hnotfun
    · exact htrusted_init x qt v hlookup hkey hlookup_v

-- Regime boundedness (imported from `FaultRobustness.lean`): tags at or above the initial
-- `nextTag` supply are outside the regime's domain (model faulty inputs only).
-- We restate it locally for convenience in this file.

-- Step theorem (context-driven, no input/output specs).
-- It assumes agreement on clean items in the initial context and preserves it
-- for the post-context, plus result agreement when the result is clean under R.
def StepFR
  (mode : LeanPoison.EvalMode)
  (ctx : TypeContext)
  (e : Expr)
  (res : TypeResult)
  (predSat : PredSat)
  (tm : TagMeaning) : Prop :=
    PredSatLaws predSat tm →
    wfTagMeaningCtx tm ctx →
    ∀ (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ θ₁ : RealizationMap)
      (cf₀ cf₁ : Config) (o₀ o₁ : Value),
      wfRealizationMap θ₀ → wfRealizationMap θ₁ →
      wfTypeContext ctx →
      runtimeInstantiatesCtx ctx μ₀ ρ₀ θ₀ → runtimeInstantiatesCtx ctx μ₁ ρ₁ θ₁ →
      regimeConsistentWithCtx ctx →
      regimeBounded ctx.regime →
      consistentWithRegime predSat ctx.regime ctx μ₀ ρ₀ θ₀ →
      consistentWithRegime predSat ctx.regime ctx μ₁ ρ₁ θ₁ →
      agreeOnClean predSat ctx.regime ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ →
      ∀ (a₀ a₁ : Address) (pm : Bool),
        wfConfig { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } →  -- initial config₀ well-formed
        wfConfig { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } →  -- initial config₁ well-formed
        terminatesTo mode e { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ →
        terminatesTo mode e { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ →
        QTypRespectsTagMeaning tm res.qualType ∧
        ∃ (θ₀' θ₁' : RealizationMap),
          wfExtendsMap θ₀ θ₀' ∧ wfExtendsMap θ₁ θ₁' ∧
          valueHasETyp θ₀' o₀ res.qualType.etyp ∧
          valueHasETyp θ₁' o₁ res.qualType.etyp ∧
          wfTagMeaningCtx tm (ctxAfter ctx res) ∧
          wfTypeContext (ctxAfter ctx res) ∧
          wfConfig cf₀ ∧  -- final config₀ well-formed
          wfConfig cf₁ ∧  -- final config₁ well-formed
          runtimeInstantiatesCtx (ctxAfter ctx res) cf₀.memory cf₀.varEnv θ₀' ∧  -- preservation
          runtimeInstantiatesCtx (ctxAfter ctx res) cf₁.memory cf₁.varEnv θ₁' ∧  -- preservation
          regimeConsistentWithCtx (ctxAfter ctx res) ∧  -- regime consistency preserved (output regime)
          consistentWithRegime predSat (ctxAfter ctx res).regime (ctxAfter ctx res) cf₀.memory cf₀.varEnv θ₀' ∧
          consistentWithRegime predSat (ctxAfter ctx res).regime (ctxAfter ctx res) cf₁.memory cf₁.varEnv θ₁' ∧
          agreeOnClean predSat (ctxAfter ctx res).regime (ctxAfter ctx res) cf₀.memory cf₀.varEnv θ₀' cf₁.memory cf₁.varEnv θ₁' ∧
          valueConsistentWithRegime predSat (ctxAfter ctx res).regime res.qualType cf₀.memory θ₀' o₀ ∧
          valueConsistentWithRegime predSat (ctxAfter ctx res).regime res.qualType cf₁.memory θ₁' o₁ ∧
          resultAgreesIfClean predSat (ctxAfter ctx res).regime cf₀.memory cf₁.memory θ₀' θ₁' res.qualType o₀ o₁

-- Step theorem spec derived from typing (context-driven).
-- No input/output specs here; they are handled by the top-level FR statement
-- and the bridge lemma.
def TypeSystemEnforcesFaultRobustness_step_spec
  (mode : LeanPoison.EvalMode)
  (e : Expr)
  (ctxᵢ : TypeContext)
  (predSat : PredSat)
  (tm : TagMeaning) : Prop :=
  ∀ (fuel : Nat) (res : TypeResult),
    typecheck .ioFree ctxᵢ e fuel = .ok res →
      StepFR mode ctxᵢ e res predSat tm

-- Local inversion lemmas for valueHasETyp (used before valueHasETyp_num_etyp is defined).
lemma valueHasETyp_etyp_num {θ : RealizationMap} {n : Int} {t : ETyp} (h : valueHasETyp θ (Value.num n) t) : t = ETyp.int := by cases h; rfl
lemma valueHasETyp_etyp_bool {θ : RealizationMap} {b : Bool} {t : ETyp} (h : valueHasETyp θ (Value.bool b) t) : t = ETyp.bool := by cases h; rfl
lemma valueHasETyp_etyp_unit {θ : RealizationMap} {t : ETyp} (h : valueHasETyp θ Value.unit t) : t = ETyp.unit := by cases h; rfl
lemma valueHasETyp_etyp_str {θ : RealizationMap} {s : String} {t : ETyp} (h : valueHasETyp θ (Value.str s) t) : t = ETyp.string := by cases h; rfl

-- Inversion for loc: avoids dependent elimination on qt.etyp in agreeValueUnder_same.
lemma valueHasETyp_loc_inv {θ : RealizationMap} {a : Address} {e : ETyp}
  (h : valueHasETyp θ (Value.loc a) e) : ∃ ls l, e = ETyp.ref ls ∧ θ.lookup l = some a ∧ l ∈ ls := by
  cases h with
  | loc hlookup hin => exact ⟨_, _, rfl, hlookup, hin⟩

-- Inversion for closure/parrow: etype is arrow/parrow (avoids dependent elimination in agreeValueUnder_same).
lemma valueHasETyp_closure_etyp_arrow {θ : RealizationMap} {x : Name} {e : Expr} {env : VarEnv} {et : ETyp}
  (h : valueHasETyp θ (Value.closure x e env) et) : et.isArrow = true := by
  cases h with
  | closure => simp [ETyp.isArrow]

lemma valueHasETyp_peClosure_etyp_parrow {θ : RealizationMap} {x : Name} {body : Expr} {env : VarEnv} {et : ETyp}
  (h : valueHasETyp θ (Value.peClosure x body env) et) : et.isParrow = true := by
  cases h with
  | peClosure => simp [ETyp.isParrow]

lemma List_lookup_some_mem
    {α β : Type} [BEq α] [LawfulBEq α]
    (x : α) (y : β) (l : List (α × β)) :
    List.lookup x l = some y → (x, y) ∈ l := by
  intro hlookup
  induction l with
  | nil =>
      simp [List.lookup] at hlookup
  | cons hd tl ih =>
      cases hd with
      | mk x' y' =>
          by_cases hEq : x == x'
          · simp [List.lookup, hEq] at hlookup
            have hx : x = x' := LawfulBEq.eq_of_beq hEq
            subst hx
            subst hlookup
            simp
          · simp [List.lookup, hEq] at hlookup
            exact List.mem_cons_of_mem _ (ih hlookup)

-- When σcap has no duplicate keys, (x,qt)::tail and tail.lookup x = some qt' is impossible.
lemma CapturedVarEnv_nodup_head_notin_tail
  (x : Name) (qt : QTyp) (tail : CapturedVarEnv) (qt' : QTyp)
  (hnd : List.Nodup (((x, qt) :: tail).map Prod.fst))
  (hσ : tail.lookup x = some qt') :
  False := by
  have hmem := List_lookup_some_mem x qt' tail (by simpa [CapturedVarEnv.lookup_eq] using hσ)
  have hx_in : x ∈ tail.map Prod.fst := List.mem_map.mpr ⟨(x, qt'), hmem, rfl⟩
  have hnd_cons := List.nodup_cons.mp hnd
  exact absurd hx_in hnd_cons.1

lemma VarTypeEnv_lookup_of_toCaptured_lookup
    (σ : VarTypeEnv) (x : Name) (qt : QTyp) :
    (VarTypeEnv.toCaptured σ).lookup x = some qt →
    σ.lookup x = some qt := by
  intro hlookup
  have hmem : (x, qt) ∈ VarTypeEnv.toCaptured σ :=
    List_lookup_some_mem x qt (VarTypeEnv.toCaptured σ) (by simpa [CapturedVarEnv.lookup_eq] using hlookup)
  exact VarTypeEnv_lookup_of_toCaptured_mem σ x qt hmem

lemma foldr_insert_domain (tenv : List (Name × QTyp)) (y : Name) (qt : QTyp) :
    (tenv.foldr (fun entry (acc : Std.ExtTreeMap Name QTyp varTypeEnvCmp) =>
      acc.insert entry.1 entry.2) ∅)[y]? = some qt →
    ∃ qt', tenv.lookup y = some qt' := by
  intro hlookup
  induction tenv with
  | nil => simp [List.foldr] at hlookup
  | cons hd tl ih =>
    simp only [List.foldr] at hlookup
    rw [Std.ExtTreeMap.getElem?_insert] at hlookup
    simp only [List.lookup]
    split at hlookup
    · rename_i hcmp
      have hkey : hd.1 = y := (LawfulEqCmp.compare_eq_iff_eq (cmp := varTypeEnvCmp)).mp hcmp
      rw [show (y == hd.1) = true from beq_iff_eq.mpr hkey.symm]
      exact ⟨hd.2, rfl⟩
    · rename_i hcmp
      have hne : hd.1 ≠ y := fun h => hcmp (h ▸ (LawfulEqCmp.compare_eq_iff_eq (cmp := varTypeEnvCmp)).mpr rfl)
      rw [show (y == hd.1) = false from beq_eq_false_iff_ne.mpr (Ne.symm hne)]
      exact ih hlookup

lemma foldr_insert_of_list_lookup (tenv : List (Name × QTyp)) (y : Name) (qt : QTyp) :
    tenv.lookup y = some qt →
    (tenv.foldr (fun entry (acc : Std.ExtTreeMap Name QTyp varTypeEnvCmp) =>
      acc.insert entry.1 entry.2) ∅)[y]? = some qt := by
  intro hlookup
  induction tenv with
  | nil => simp [List.lookup] at hlookup
  | cons hd tl ih =>
    simp only [List.foldr, List.lookup] at hlookup ⊢
    rw [Std.ExtTreeMap.getElem?_insert]
    split at hlookup
    · rename_i hbeq
      have hkey : y = hd.1 := beq_iff_eq.mp hbeq
      rw [show varTypeEnvCmp hd.1 y = .eq from
        (LawfulEqCmp.compare_eq_iff_eq (cmp := varTypeEnvCmp)).mpr hkey.symm]
      simpa using hlookup
    · rename_i hbeq
      have hne : y ≠ hd.1 := beq_eq_false_iff_ne.mp hbeq
      have hcmp_ne : ¬(varTypeEnvCmp hd.1 y = .eq) :=
        fun hcmp => hne ((LawfulEqCmp.compare_eq_iff_eq (cmp := varTypeEnvCmp)).mp hcmp).symm
      rw [if_neg hcmp_ne]
      exact ih hlookup

lemma list_lookup_exists_of_ofCaptured_lookup
    (tenv : CapturedVarEnv) (y : Name) (qt : QTyp) :
    (VarTypeEnv.ofCaptured tenv).lookup y = some qt →
    ∃ qt', tenv.lookup y = some qt' :=
  foldr_insert_domain tenv y qt

lemma ofCaptured_lookup_of_list_lookup
    (tenv : CapturedVarEnv) (y : Name) (qt : QTyp) :
    tenv.lookup y = some qt →
    (VarTypeEnv.ofCaptured tenv).lookup y = some qt :=
  foldr_insert_of_list_lookup tenv y qt

lemma list_lookup_of_ofCaptured_lookup
    (tenv : CapturedVarEnv) (y : Name) (qt : QTyp) :
    (VarTypeEnv.ofCaptured tenv).lookup y = some qt →
    tenv.lookup y = some qt := by
  intro hlookup
  rcases list_lookup_exists_of_ofCaptured_lookup tenv y qt hlookup with ⟨qt', hlist⟩
  have hlookup' : (VarTypeEnv.ofCaptured tenv).lookup y = some qt' :=
    ofCaptured_lookup_of_list_lookup tenv y qt' hlist
  have hqt : qt' = qt := by
    have : some qt' = some qt := by simpa [hlookup'] using hlookup
    exact Option.some.inj this
  simpa [hqt] using hlist

/-- Path D helper: build direct member `varsRegime` facts for the singleton closure captured env
created at lambda typing sites, from the enclosing `consistentWithRegime`. -/
lemma memberVarsRegimeEvidence_of_toCaptured
  (predSat : PredSat) (R : Regime) (ctx : TypeContext)
  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (hcwr : consistentWithRegime predSat R ctx μ ρ θ) :
  MemberVarsRegimeEvidence predSat R μ (VarTypeEnv.toCaptured ctx.varEnv) ρ := by
  intro y qt_y k_y v_y hlookup_σ hlookup_ρ hguard hkR
  have hlookup_list :
      (VarTypeEnv.toCaptured ctx.varEnv).lookup y = some qt_y :=
    list_lookup_of_ofCaptured_lookup (VarTypeEnv.toCaptured ctx.varEnv) y qt_y hlookup_σ
  exact hcwr.2.1 y qt_y k_y
    (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt_y hlookup_list)
    hguard hkR

/-- Path D helper: build direct member `closureCapturedVarsRegime` facts for the singleton closure
captured env created at lambda typing sites, from the enclosing `consistentWithRegime`. -/
lemma memberCvcrEvidence_of_toCaptured
  (predSat : PredSat) (R : Regime) (ctx : TypeContext)
  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (hcwr : consistentWithRegime predSat R ctx μ ρ θ) :
  MemberCvcrEvidence predSat R μ θ (VarTypeEnv.toCaptured ctx.varEnv) ρ := by
  intro y qt_y v_y hlookup_σ hlookup_ρ
  have hlookup_list :
      (VarTypeEnv.toCaptured ctx.varEnv).lookup y = some qt_y :=
    list_lookup_of_ofCaptured_lookup (VarTypeEnv.toCaptured ctx.varEnv) y qt_y hlookup_σ
  exact hcwr.2.2 y qt_y v_y
    (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt_y hlookup_list)
    hlookup_ρ

lemma agreeCapturedEnv_same
  (predSat : PredSat) (R : Regime) (μ : Memory) (θ : RealizationMap)
  (σcap : CapturedVarEnv) (ρcap : VarEnv)
  (hnd : List.Nodup (σcap.map Prod.fst))
  (hcover : ∀ y qt, σcap.lookup y = some qt → ∃ v, ρcap.lookup y = some v)
  (hhenv : ∀ y qt v, σcap.lookup y = some qt → ρcap.lookup y = some v → valueHasETyp θ v qt.etyp)
  (hagree : ∀ y qt v, σcap.lookup y = some qt → ρcap.lookup y = some v → qtypCleanUnder R qt →
    valueHasETyp θ v qt.etyp → agreeValueUnder predSat R μ μ θ θ qt v v) :
  agreeCapturedEnv predSat R μ μ θ θ σcap ρcap ρcap := by
  induction σcap with
  | nil => exact agreeCapturedEnv.nil
  | cons entry tail ih =>
    rcases entry with ⟨x, qt⟩
    have hnd_tail : List.Nodup (tail.map Prod.fst) := (List.nodup_cons.mp hnd).2
    rcases hcover x qt (by simp [CapturedVarEnv.lookup_eq, List.lookup]) with ⟨v, hlookup⟩
    have htyp : valueHasETyp θ v qt.etyp := hhenv x qt v (by simp [CapturedVarEnv.lookup_eq, List.lookup]) hlookup
    by_cases hclean : qtypCleanUnder R qt
    · refine agreeCapturedEnv.cons_clean hclean hlookup hlookup htyp htyp ?_ (ih hnd_tail ?_ ?_ (fun y qt' v' hσ_tail hρ hclean' htyp' =>
        hagree y qt' v' (by
          simp only [CapturedVarEnv.lookup_eq, List.lookup] at hσ_tail ⊢
          split at ⊢
          · have heq : y = x := beq_iff_eq.mp (by assumption)
            exfalso; rw [heq] at hσ_tail
            have hmem : (x, qt') ∈ tail := List_lookup_some_mem x qt' tail hσ_tail
            exact (List.nodup_cons.mp hnd).1 (List.mem_map.mpr ⟨(x, qt'), hmem, rfl⟩)
          · exact hσ_tail) hρ hclean' htyp'))
      · exact hagree x qt v (by simp [CapturedVarEnv.lookup_eq, List.lookup]) hlookup hclean htyp
      · intro y qt' h
        by_cases heq : (y == x) = true
        · obtain ⟨v', hv'⟩ := hcover x qt (by simp only [CapturedVarEnv.lookup_eq, List.lookup, beq_self_eq_true])
          exact ⟨v', by rw [beq_iff_eq.mp heq]; exact hv'⟩
        · obtain ⟨v', hv'⟩ := hcover y qt' (by simp only [heq, CapturedVarEnv.lookup_eq, List.lookup]; exact h)
          exact ⟨v', hv'⟩
      · intro y qt' v' hσ hρ
        by_cases heq : (y == x) = true
        · exact False.elim (CapturedVarEnv_nodup_head_notin_tail x qt tail qt' hnd (by simpa [CapturedVarEnv.lookup_eq, beq_iff_eq.mp heq] using hσ))
        · exact hhenv y qt' v' (by simp only [heq, CapturedVarEnv.lookup_eq, List.lookup]; exact hσ) hρ
    · refine agreeCapturedEnv.cons_dirty hclean hlookup hlookup htyp htyp (ih hnd_tail ?_ ?_ (fun y qt' v' hσ_tail hρ hclean' htyp' =>
        hagree y qt' v' (by
          simp only [CapturedVarEnv.lookup_eq, List.lookup] at hσ_tail ⊢
          split at ⊢
          · have heq : y = x := beq_iff_eq.mp (by assumption)
            exfalso; rw [heq] at hσ_tail
            have hmem : (x, qt') ∈ tail := List_lookup_some_mem x qt' tail hσ_tail
            exact (List.nodup_cons.mp hnd).1 (List.mem_map.mpr ⟨(x, qt'), hmem, rfl⟩)
          · exact hσ_tail) hρ hclean' htyp'))
      · intro y qt' hy
        by_cases heq : (y == x) = true
        · obtain ⟨v', hv'⟩ := hcover x qt (by simp only [CapturedVarEnv.lookup_eq, List.lookup, beq_self_eq_true])
          exact ⟨v', by rw [beq_iff_eq.mp heq]; exact hv'⟩
        · exact hcover y qt' (by simp only [heq, CapturedVarEnv.lookup_eq, List.lookup]; exact hy)
      · intro y qt' v' hσ hρ
        by_cases heq : (y == x) = true
        · exact False.elim (CapturedVarEnv_nodup_head_notin_tail x qt tail qt' hnd (by simpa [CapturedVarEnv.lookup_eq, beq_iff_eq.mp heq] using hσ))
        · exact hhenv y qt' v' (by simp only [heq, CapturedVarEnv.lookup_eq, List.lookup]; exact hσ) hρ

-- Auxiliary: builds agreeValueUnder from deepValueQTypProperty evidence (induction on the tree).
-- This resolves the mutual recursion that previously required sorry in agreeCapturedEnv_same_toCaptured.
-- Note: hclean and htyp are in the conclusion (not parameters) so that induction on hdeep
-- automatically generalizes them without needing manual revert/intro.
lemma agreeValueUnder_same_aux
    {predSat : PredSat} {R : Regime} {μ : Memory} {θ : RealizationMap}
    {qt : QTyp} {v : Value}
    (hdeep : deepValueQTypProperty (fun σcap ρcap =>
      capturedVarsRegimeProperty predSat R μ σcap ρcap ∧
      capturedVarsTypingProperty θ σcap ρcap) qt v) :
    qtypCleanUnder R qt → valueHasETyp θ v qt.etyp →
    agreeValueUnder predSat R μ μ θ θ qt v v := by
  induction hdeep with
  | @nonClosure _qt' v' hnclos hnclospe =>
    intro hclean htyp
    cases hclean with
    | clean hpoison =>
      cases v' with
      | num n =>
        have hetyp := valueHasETyp_etyp_num htyp
        exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison (by rw [hetyp]; rfl) (fun ⟨_, h⟩ => by rw [hetyp] at h; injection h) rfl
      | bool _ =>
        have hetyp := valueHasETyp_etyp_bool htyp
        exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison (by rw [hetyp]; rfl) (fun ⟨_, h⟩ => by rw [hetyp] at h; injection h) rfl
      | unit =>
        have hetyp := valueHasETyp_etyp_unit htyp
        exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison (by rw [hetyp]; rfl) (fun ⟨_, h⟩ => by rw [hetyp] at h; injection h) rfl
      | str _ =>
        have hetyp := valueHasETyp_etyp_str htyp
        exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison (by rw [hetyp]; rfl) (fun ⟨_, h⟩ => by rw [hetyp] at h; injection h) rfl
      | loc a =>
        rcases valueHasETyp_loc_inv htyp with ⟨_ls, l, hetyp, hlookup, hin⟩
        exact agreeValueUnder.clean_ref hpoison hetyp hlookup hin rfl hlookup rfl
      | closure x body env => exact absurd rfl (hnclos x body env)
      | peClosure x body env => exact absurd rfl (hnclospe x body env)
    | guard k htag hregime _hnotfun =>
      cases v' with
      | num n =>
        have hetyp := valueHasETyp_etyp_num htyp
        exact agreeValueUnder.withPred_true_eq k htag hregime (by rw [hetyp]; rfl) (fun ⟨_, h⟩ => by rw [hetyp] at h; injection h) rfl
      | bool _ =>
        have hetyp := valueHasETyp_etyp_bool htyp
        exact agreeValueUnder.withPred_true_eq k htag hregime (by rw [hetyp]; rfl) (fun ⟨_, h⟩ => by rw [hetyp] at h; injection h) rfl
      | unit =>
        have hetyp := valueHasETyp_etyp_unit htyp
        exact agreeValueUnder.withPred_true_eq k htag hregime (by rw [hetyp]; rfl) (fun ⟨_, h⟩ => by rw [hetyp] at h; injection h) rfl
      | str _ =>
        have hetyp := valueHasETyp_etyp_str htyp
        exact agreeValueUnder.withPred_true_eq k htag hregime (by rw [hetyp]; rfl) (fun ⟨_, h⟩ => by rw [hetyp] at h; injection h) rfl
      | loc a =>
        rcases valueHasETyp_loc_inv htyp with ⟨_ls, l, hetyp, hlookup, hin⟩
        exact agreeValueUnder.withPred_true_ref k htag hregime hetyp hlookup hin rfl hlookup rfl
      | closure x body env => exact absurd rfl (hnclos x body env)
      | peClosure x body env => exact absurd rfl (hnclospe x body env)
  | @closure qt' _v' xp body ρcap σcap st1 st2 p tcls hval hetyp_eq hmem hP hSub ih =>
    subst hval
    intro _hclean htyp
    obtain ⟨hRegime, hnd, hcover, hhenv⟩ := hP
    by_cases hdirty : ¬internalPoisonClean qt'
    · exact agreeValueUnder.dirty_internal_arrow hdirty
        (by rw [hetyp_eq]; rfl) htyp htyp
    · have h_clean_int : internalPoisonClean qt' := by by_contra h; exact hdirty h
      have hcap : agreeCapturedEnv predSat R μ μ θ θ σcap ρcap ρcap :=
        agreeCapturedEnv_same predSat R μ θ σcap ρcap hnd hcover hhenv
          (fun y qt_y v_y hσ hρ hclean_y htyp_y => ih y qt_y v_y hσ hρ hclean_y htyp_y)
      have hmemberVars : MemberVarsRegimeEvidence predSat R μ σcap ρcap := by
        intro y qt_y k_y v_y hlookup_σ _hlookup_ρ hguard hkR
        exact hRegime y qt_y k_y
          (list_lookup_of_ofCaptured_lookup σcap y qt_y hlookup_σ) hguard hkR
      have hmemberCvcr : MemberCvcrEvidence predSat R μ θ σcap ρcap := by
        intro y qt_y v_y hlookup_σ hlookup_ρ
        exact .intro (hSub y qt_y v_y
          (list_lookup_of_ofCaptured_lookup σcap y qt_y hlookup_σ) hlookup_ρ)
      exact agreeValueUnder.clean_internal_arrow h_clean_int hetyp_eq hmem rfl
        hcap hmemberVars hmemberCvcr hmemberVars hmemberCvcr rfl rfl
  | @peClosure qt' _v' xp body pbody ρcap σcap st1 st2 p tcls hval hetyp_eq hpure_deep hmem hP hSub ih =>
    subst hval
    intro _hclean htyp
    obtain ⟨hRegime, hnd, hcover, hhenv⟩ := hP
    by_cases hdirty : ¬internalPoisonClean qt'
    · exact agreeValueUnder.dirty_internal_parrow hdirty
        (by rw [hetyp_eq]; rfl) htyp htyp
    · have h_clean_int : internalPoisonClean qt' := by by_contra h; exact hdirty h
      have hcap : agreeCapturedEnv predSat R μ μ θ θ σcap ρcap ρcap :=
        agreeCapturedEnv_same predSat R μ θ σcap ρcap hnd hcover hhenv
          (fun y qt_y v_y hσ hρ hclean_y htyp_y => ih y qt_y v_y hσ hρ hclean_y htyp_y)
      have hmemberVars : MemberVarsRegimeEvidence predSat R μ σcap ρcap := by
        intro y qt_y k_y v_y hlookup_σ _hlookup_ρ hguard hkR
        exact hRegime y qt_y k_y
          (list_lookup_of_ofCaptured_lookup σcap y qt_y hlookup_σ) hguard hkR
      have hmemberCvcr : MemberCvcrEvidence predSat R μ θ σcap ρcap := by
        intro y qt_y v_y hlookup_σ hlookup_ρ
        exact .intro (hSub y qt_y v_y
          (list_lookup_of_ofCaptured_lookup σcap y qt_y hlookup_σ) hlookup_ρ)
      exact agreeValueUnder.clean_internal_parrow h_clean_int hetyp_eq hmem ⟨hpure_deep, rfl⟩
        hcap hmemberVars hmemberCvcr hmemberVars hmemberCvcr rfl rfl

-- Reflexive agreement when both sides are the same config.
-- Uses closureCapturedVarsRegime evidence (which carries both regime and typing info for a single σcap)
-- to build agreeCapturedEnv, resolving the member-matching problem.
lemma agreeValueUnder_same
    {predSat : PredSat} {R : Regime} {μ : Memory} {θ : RealizationMap}
    {qt : QTyp} {v : Value} (hclean : qtypCleanUnder R qt) (htyp : valueHasETyp θ v qt.etyp)
    (hcvcr : closureCapturedVarsRegime predSat R qt μ θ v) :
    agreeValueUnder predSat R μ μ θ θ qt v v := by
  obtain ⟨hdeep⟩ := hcvcr
  exact agreeValueUnder_same_aux hdeep hclean htyp

-- agreeOnClean when both sides are the same (μ, ρ, θ).
lemma agreeOnClean_same_config
  (predSat : PredSat) (R : Regime) (ctx : TypeContext) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (hric : runtimeInstantiatesCtx ctx μ ρ θ) (hcwr : consistentWithRegime predSat R ctx μ ρ θ)
  (_hR : R = ctx.regime) :
  agreeOnClean predSat R ctx μ ρ θ μ ρ θ := by
  constructor
  · intro l qt hlookup hclean
    cases hθ : θ.lookup l with
    | none => exact agreeLocUnder.both_unrealized l qt hθ hθ
    | some a =>
      have hcontains := (hric.1 l a hθ).2
      have hmem : a ∈ μ := (ExtTreeMap.contains_iff_mem).1 hcontains
      have hisSome : μ[a]?.isSome = true := (ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
      cases hμan : μ[a]? with
      | none => simp only [hμan] at hisSome; exact False.elim (Bool.false_ne_true hisSome)
      | some n =>
        by_cases hetyp : qt.etyp = ETyp.int
        · have hμ : Memory.lookup μ a = some n := by simp [Memory.lookup, ExtTreeMap.get?_eq_getElem?, hμan]
          have htyp : valueHasETyp θ (Value.num n) qt.etyp := by rw [hetyp]; exact valueHasETyp.num n
          have hcvcr : closureCapturedVarsRegime predSat R qt μ θ (Value.num n) :=
            .intro (.nonClosure (fun _ _ _ h => by injection h) (fun _ _ _ h => by injection h))
          exact agreeLocUnder.agree_values l qt a a n n hθ hθ hμ hμ
            (agreeValueUnder_same hclean htyp hcvcr)
        · exact False.elim (hetyp (memEnv_lookup_etyp_int ctx.memEnv l qt hlookup))
  · intro x qt hlookup hclean
    rcases hric.2 hlookup with ⟨v, hρ, htyp⟩
    have hcvcr := hcwr.2.2 x qt v hlookup hρ
    refine agreeVarUnder.agree_values x qt v v hρ hρ
      (agreeValueUnder_same hclean htyp hcvcr)

-- Unary preservation: a single run preserves the value at an inherited clean location.
inductive PreservesInheritedCleanLocOneRun
  (μ_in μ_out : Memory) (θ_in θ_out : RealizationMap) (l : Loc) : Prop where
  | both_unrealized (h_in : θ_in.lookup l = none) (h_out : θ_out.lookup l = none)
  | preserve_value (a : Address) (n : Int)
      (h_in : θ_in.lookup l = some a) (h_mem_in : μ_in.lookup a = some n)
      (h_out : θ_out.lookup l = some a) (h_mem_out : μ_out.lookup a = some n)

lemma PreservesInheritedCleanLocOneRun.trans
  {μ₀ μ₁ μ₂ : Memory} {θ₀ θ₁ θ₂ : RealizationMap} {l : Loc}
  (h₀₁ : PreservesInheritedCleanLocOneRun μ₀ μ₁ θ₀ θ₁ l)
  (h₁₂ : PreservesInheritedCleanLocOneRun μ₁ μ₂ θ₁ θ₂ l) :
  PreservesInheritedCleanLocOneRun μ₀ μ₂ θ₀ θ₂ l := by
  cases h₀₁ with
  | both_unrealized hnone₀ hnone₁ =>
      cases h₁₂ with
      | both_unrealized hnone₁' hnone₂ =>
          exact .both_unrealized hnone₀ hnone₂
      | preserve_value _ _ hsome₁ _ _ _ =>
          exact False.elim (Option.noConfusion (hnone₁.symm.trans hsome₁))
  | preserve_value a n hθ₀ hm₀ hθ₁ hm₁ =>
      cases h₁₂ with
      | both_unrealized hnone₁ _ =>
          exact False.elim (Option.noConfusion (hθ₁.symm.trans hnone₁))
      | preserve_value a' n' hθ₁' hm₁' hθ₂ hm₂ =>
          have ha : a' = a := Option.some.inj (hθ₁'.symm.trans hθ₁)
          have hn : n' = n := by
            rw [ha] at hm₁'
            exact Option.some.inj (hm₁'.symm.trans hm₁)
          subst ha
          subst hn
          exact .preserve_value a' n' hθ₀ hm₀ hθ₂ hm₂

inductive PreservesInheritedFinalCleanLocsOneRun
  (ctx : TypeContext) (res : TypeResult)
  (μ_in μ_out : Memory) (θ_in θ_out : RealizationMap) : Prop where
  | intro (hpres : ∀ l qt_in qt_out,
      ctx.memEnv.lookup l = some qt_in →
      res.memEnv'.lookup l = some qt_out →
      qtypCleanUnder res.regime' qt_out →
      PreservesInheritedCleanLocOneRun μ_in μ_out θ_in θ_out l)

lemma PreservesInheritedFinalCleanLocsOneRun.apply
  {ctx : TypeContext} {res : TypeResult}
  {μ_in μ_out : Memory} {θ_in θ_out : RealizationMap}
  (hpres :
    PreservesInheritedFinalCleanLocsOneRun ctx res μ_in μ_out θ_in θ_out)
  {l : Loc} {qt_in qt_out : QTyp}
  (hlookup_in : ctx.memEnv.lookup l = some qt_in)
  (hlookup_out : res.memEnv'.lookup l = some qt_out)
  (hclean_out : qtypCleanUnder res.regime' qt_out) :
  PreservesInheritedCleanLocOneRun μ_in μ_out θ_in θ_out l := by
  rcases hpres with ⟨hpres⟩
  exact hpres l qt_in qt_out hlookup_in hlookup_out hclean_out

lemma PreservesInheritedFinalCleanLocsOneRun.refl
  {ctx : TypeContext} {res : TypeResult}
  {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
  (hric : runtimeInstantiatesCtx ctx μ ρ θ) :
  PreservesInheritedFinalCleanLocsOneRun ctx res μ μ θ θ := by
  refine ⟨?_⟩
  intro l _qt_in _qt_out _hlookup_in _hlookup_out _hclean_out
  cases hθ : θ.lookup l with
  | none =>
      exact .both_unrealized hθ hθ
  | some a =>
      have hcontains_a : μ.contains a = true := (hric.1 l a hθ).2
      have hmem : a ∈ μ := (ExtTreeMap.contains_iff_mem).1 hcontains_a
      have hisSome : μ[a]?.isSome = true := (ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
      cases hlookup_mem_raw : μ[a]? with
      | none =>
          simp [hlookup_mem_raw] at hisSome
      | some n =>
          have hlookup_mem : μ.lookup a = some n := by
            simp [Memory.lookup, ExtTreeMap.get?_eq_getElem?, hlookup_mem_raw]
          exact .preserve_value a n hθ hlookup_mem hθ hlookup_mem

lemma PreservesInheritedFinalCleanLocsOneRun.compose
  {ctx : TypeContext} {res1 res2 : TypeResult}
  {μ₀ μ₁ μ₂ : Memory} {θ₀ θ₁ θ₂ : RealizationMap}
  (hclean_back :
    ∀ l qt_in qt_out,
      ctx.memEnv.lookup l = some qt_in →
      res2.memEnv'.lookup l = some qt_out →
      qtypCleanUnder res2.regime' qt_out →
      ∃ qt_mid, res1.memEnv'.lookup l = some qt_mid ∧ qtypCleanUnder res1.regime' qt_mid)
  (hpres₀₁ : PreservesInheritedFinalCleanLocsOneRun ctx res1 μ₀ μ₁ θ₀ θ₁)
  (hpres₁₂ : PreservesInheritedFinalCleanLocsOneRun (ctxAfter ctx res1) res2 μ₁ μ₂ θ₁ θ₂) :
  PreservesInheritedFinalCleanLocsOneRun ctx res2 μ₀ μ₂ θ₀ θ₂ := by
  refine ⟨?_⟩
  intro l qt_in qt_out hlookup_in hlookup_out hclean_out
  rcases hclean_back l qt_in qt_out hlookup_in hlookup_out hclean_out with
    ⟨qt_mid, hlookup_mid, hclean_mid⟩
  have hpres_mid :
      PreservesInheritedCleanLocOneRun μ₀ μ₁ θ₀ θ₁ l :=
    PreservesInheritedFinalCleanLocsOneRun.apply
      (ctx := ctx) (res := res1) (μ_in := μ₀) (μ_out := μ₁) (θ_in := θ₀) (θ_out := θ₁)
      hpres₀₁ hlookup_in hlookup_mid hclean_mid
  have hpres_final :
      PreservesInheritedCleanLocOneRun μ₁ μ₂ θ₁ θ₂ l :=
    PreservesInheritedFinalCleanLocsOneRun.apply
      (ctx := ctxAfter ctx res1) (res := res2)
      (μ_in := μ₁) (μ_out := μ₂) (θ_in := θ₁) (θ_out := θ₂)
      hpres₁₂
      (by simpa [ctxAfter] using hlookup_mid)
      hlookup_out
      hclean_out
  exact PreservesInheritedCleanLocOneRun.trans hpres_mid hpres_final

lemma singleRunFinalCleanWitness_of_same_state
  {ctx : TypeContext} {res : TypeResult}
  {predSat : PredSat} {tm : TagMeaning}
  {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
  {cf : Config} {o : Value}
  {a : Address} {pm : Bool}
  (hctxAfter : ctxAfter ctx res = ctx)
  (hcf : cf = { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm })
  (hvaltyp : valueHasETyp θ o res.qualType.etyp)
  (hvalc : valueConsistentWithRegime predSat ctx.regime res.qualType μ θ o)
  (_hwfTm : wfTagMeaningCtx tm ctx)
  (_hwf : wfTypeContext ctx)
  (hric : runtimeInstantiatesCtx ctx μ ρ θ)
  (_hreg : regimeConsistentWithCtx ctx)
  (hcwr : consistentWithRegime predSat ctx.regime ctx μ ρ θ)
  (_hwfcfg : wfConfig { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm }) :
  ∃ (θ' : RealizationMap),
    wfExtendsMap θ θ' ∧
    valueHasETyp θ' o res.qualType.etyp ∧
    runtimeInstantiatesCtx (ctxAfter ctx res) cf.memory cf.varEnv θ' ∧
    consistentWithRegime predSat (ctxAfter ctx res).regime (ctxAfter ctx res) cf.memory cf.varEnv θ' ∧
    valueConsistentWithRegime predSat (ctxAfter ctx res).regime res.qualType cf.memory θ' o ∧
    PreservesInheritedFinalCleanLocsOneRun ctx res μ cf.memory θ θ' := by
  refine ⟨θ, ?_, hvaltyp, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun _ _ hlookup => hlookup, fun hθwf => hθwf⟩
  · simpa [hctxAfter, hcf] using hric
  · simpa [hctxAfter, hcf] using hcwr
  · simpa [hctxAfter, hcf] using hvalc
  · simpa [hcf] using (PreservesInheritedFinalCleanLocsOneRun.refl (ctx := ctx) (res := res) (ρ := ρ) hric)

def StepFRSingleRunFinalCleanPcTrue
  (mode : LeanPoison.EvalMode)
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
      regimeBounded ctx.regime →
      consistentWithRegime predSat ctx.regime ctx μ ρ θ →
      ∀ (a : Address) (pm : Bool),
        wfConfig { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } →
        terminatesTo mode e { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o →
        ctx.pc = true →
        ∃ (θ' : RealizationMap),
          wfExtendsMap θ θ' ∧
          valueHasETyp θ' o res.qualType.etyp ∧
          runtimeInstantiatesCtx (ctxAfter ctx res) cf.memory cf.varEnv θ' ∧
          consistentWithRegime predSat (ctxAfter ctx res).regime (ctxAfter ctx res) cf.memory cf.varEnv θ' ∧
          valueConsistentWithRegime predSat (ctxAfter ctx res).regime res.qualType cf.memory θ' o ∧
          PreservesInheritedFinalCleanLocsOneRun ctx res μ cf.memory θ θ'

section TypeSystemEnforcesFaultRobustness_impl_proof

-- Helper lemmas: transport predicate-based properties across qualified types
-- that differ only in irrelevant fields (e.g. poison), but share the same predicate.

lemma qtypGuardTag_of_pred_eq {qt qt' : QTyp}
  (hpred : qt.pred = qt'.pred) :
  qtypGuardTag qt = qtypGuardTag qt' := by
  cases qt with
  | mk et p pred =>
    cases qt' with
    | mk et' p' pred' =>
      -- qtypGuardTag depends only on the predicate field
      simp [qtypGuardTag] at hpred ⊢
      cases hpred
      rfl

lemma qtypPredHolds_transport_pred
  {predSat : PredSat} {qt qt' : QTyp} {μ : Memory} {v : Value}
  (hpred : qt.pred = qt'.pred) :
  qtypPredHolds predSat qt μ v → qtypPredHolds predSat qt' μ v := by
  intro h
  cases h with
  | noPred_ok hnp =>
      refine qtypPredHolds.noPred_ok (qt := qt') ?_
      calc
        qt'.pred = qt.pred := by simp [hpred]
        _ = Predicate.noPred := by exact hnp
  | guardClosure_ok hclos hsat =>
      rename_i k arg_name pred_body var_env
      refine qtypPredHolds.guardClosure_ok (qt := qt') (k := k) (arg_name := arg_name)
        (pred_body := pred_body) (var_env := var_env) ?_ hsat
      calc
        qt'.pred = qt.pred := by simp [hpred]
        _ = Predicate.guardClosure k arg_name pred_body var_env := by exact hclos
  | guardOnly_ok hgo hsat =>
      rename_i k
      refine qtypPredHolds.guardOnly_ok (qt := qt') (k := k) ?_ hsat
      calc
        qt'.pred = qt.pred := by simp [hpred]
        _ = Predicate.guardOnly k := by exact hgo

lemma qtypPredHolds_transport_pred_not
  {predSat : PredSat} {qt qt' : QTyp} {μ : Memory} {v : Value}
  (hpred : qt.pred = qt'.pred) :
  (¬ qtypPredHolds predSat qt μ v) → (¬ qtypPredHolds predSat qt' μ v) := by
  intro hnot hholds
  -- Transport back to `qt` and contradict.
  have hback : qtypPredHolds predSat qt μ v :=
    qtypPredHolds_transport_pred (predSat := predSat) (qt := qt') (qt' := qt) (μ := μ) (v := v) (by simp [hpred]) hholds
  exact hnot hback

lemma predSat_mem_noPred_compat
  {predSat : PredSat} {tm : TagMeaning}
  (hpredlaws : PredSatLaws predSat tm)
  (θ : RealizationMap) :
  ∀ (k : Tag) (μ μ' : Memory) (v : Value), predSat k μ v ↔ predSat k μ' v := by
  intro k μ μ' v
  exact
    hpredlaws.mem_monotone (k := k) (pred := Predicate.noPred) (fuel := 0) (μ := μ) (μ' := μ') (v := v)
      (deps := LocSet.empty) (θ := θ) (by simp [extractDepsFromPred, pure, Except.pure])
      (by intro l hl; cases hl)

lemma qtypPredHolds_mem_compat_of_predSatLaws
  {predSat : PredSat} {tm : TagMeaning}
  (hpredlaws : PredSatLaws predSat tm)
  (θ : RealizationMap) (μ μ' : Memory) :
  ∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ v ↔ qtypPredHolds predSat qt μ' v := by
  have hPredSat_mem :
      ∀ (k : Tag) (μ₀ μ₁ : Memory) (v : Value), predSat k μ₀ v ↔ predSat k μ₁ v := by
    intro k μ₀ μ₁ v
    exact predSat_mem_noPred_compat hpredlaws θ k μ₀ μ₁ v
  intro qt v
  constructor <;> intro h
  · cases h with
    | noPred_ok hp =>
        exact qtypPredHolds.noPred_ok hp
    | guardClosure_ok hp hs =>
        exact qtypPredHolds.guardClosure_ok hp ((hPredSat_mem _ _ _ v).1 hs)
    | guardOnly_ok hp hs =>
        exact qtypPredHolds.guardOnly_ok hp ((hPredSat_mem _ _ _ v).1 hs)
  · cases h with
    | noPred_ok hp =>
        exact qtypPredHolds.noPred_ok hp
    | guardClosure_ok hp hs =>
        exact qtypPredHolds.guardClosure_ok hp ((hPredSat_mem _ _ _ v).2 hs)
    | guardOnly_ok hp hs =>
        exact qtypPredHolds.guardOnly_ok hp ((hPredSat_mem _ _ _ v).2 hs)

lemma not_qtypCleanUnder_of_poison_true_noPred
  {R : Regime} {qt : QTyp}
  (hpoison : qt.poison = true)
  (hpred : qt.pred = Predicate.noPred) :
  ¬ qtypCleanUnder R qt := by
  intro hclean
  cases hclean with
  | clean hpoison' =>
      simp [hpoison] at hpoison'
  | guard _ htag _ _ =>
      simp [qtypGuardTag, hpred] at htag

lemma list_fold_joinPredicates_init_noPred
  (env : MemoryTypeEnv) (xs : List Loc) (storedPoison : Poison) :
  ((xs.foldl
      (fun acc l0 =>
        match env[l0]? with
        | some qt0 => (joinPoison acc.1 qt0.poison, joinPredicates acc.2 qt0.pred)
        | none => acc)
      (storedPoison, Predicate.noPred)).2) = Predicate.noPred := by
  induction xs generalizing storedPoison with
  | nil =>
      simp
  | cons x xs ih =>
      cases hget : env[x]? with
      | none =>
          simpa [List.foldl, hget] using ih storedPoison
      | some qtX =>
          simpa [List.foldl, hget, joinPredicates] using ih (joinPoison storedPoison qtX.poison)

-- Monotonicity of capturedVarsRegimeProperty under Regime.monotoneStep.
lemma capturedVarsRegimeProperty_monotone
  {predSat : PredSat} {R R' : Regime} {μ : Memory}
  (h_mono : Regime.monotoneStep R R')
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (h : capturedVarsRegimeProperty predSat R μ σcap ρcap) :
  capturedVarsRegimeProperty predSat R' μ σcap ρcap := by
  intro x qt_x k_x hlook hguard hkR'
  have hkR : R.lookup? k_x ≠ none := fun habs => h_mono.2.2 k_x hkR' habs
  have hvr_R := h x qt_x k_x hlook hguard hkR
  obtain ⟨b, hb⟩ : ∃ b, R.lookup? k_x = some b := by
    cases h_eq : R.lookup? k_x with
    | none => exact absurd h_eq hkR
    | some b => exact ⟨b, rfl⟩
  cases h_mono.2.1 k_x b hb with
  | inl hk'_eq => exact varsRegime_monotone h_mono hguard hb hk'_eq hvr_R
  | inr hk'_none => exact absurd hk'_none hkR'

lemma closureCapturedVarsRegime_monotone
  {predSat : PredSat} {R R' : Regime} {qt : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  (h_mono : Regime.monotoneStep R R')
  (h : closureCapturedVarsRegime predSat R qt μ θ v) :
  closureCapturedVarsRegime predSat R' qt μ θ v := by
  cases h with
  | intro hdeep =>
      exact .intro (deepValueQTypProperty_mono
        (fun σcap ρcap ⟨hP, hT⟩ => ⟨capturedVarsRegimeProperty_monotone h_mono hP, hT⟩)
        hdeep)

-- Lookup-back transport helpers used by both the `ite` and join transport proofs.
lemma varsRegime_transport_active_lookup_back
  {predSat : PredSat} {R R' : Regime} {μ : Memory} {ρ : VarEnv}
  {entry : Name × QTyp} {k : Tag} {b : Bool}
  (hlookup_back : ∀ k b, R'.lookup? k = some b → R.lookup? k = some b)
  (hguard : qtypGuardTag entry.snd = some k)
  (hreg' : R'.lookup? k = some b)
  (h : varsRegime predSat R μ ρ entry) :
  varsRegime predSat R' μ ρ entry := by
  cases h with
  | noPred_ok hpred =>
      rw [hpred] at hguard
      cases hguard
  | guardOnly_ok k' hgo =>
      exact varsRegime.guardOnly_ok entry k' hgo
  | withPred_ok k' arg_name pred_body var_env v b' hclos hreg hvar hcons =>
      have hk_eq : k' = k := by
        have : some k' = some k := by
          calc
            some k' = qtypGuardTag entry.snd := by simp [qtypGuardTag, hclos]
            _ = some k := hguard
        exact Option.some.inj this
      have hreg_back : R.lookup? k = some b := hlookup_back k b hreg'
      have hb_eq : b' = b := by
        have : some b' = some b := by
          calc
            some b' = R.lookup? k' := by symm; exact hreg
            _ = R.lookup? k := by simp [hk_eq]
            _ = some b := hreg_back
        exact Option.some.inj this
      have hreg'' : R'.lookup? k' = some b' := by
        simp [hk_eq, hb_eq] at hreg' ⊢
        exact hreg'
      exact varsRegime.withPred_ok entry k' arg_name pred_body var_env v b' hclos hreg'' hvar hcons

lemma capturedVarsRegimeProperty_transport_lookup_back
  {predSat : PredSat} {R R' : Regime} {μ : Memory}
  (hlookup_back : ∀ k b, R'.lookup? k = some b → R.lookup? k = some b)
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (h : capturedVarsRegimeProperty predSat R μ σcap ρcap) :
  capturedVarsRegimeProperty predSat R' μ σcap ρcap := by
  intro x qt_x k_x hlook hguard hkR'
  cases hkR'some : R'.lookup? k_x with
  | none =>
      exact (hkR' hkR'some).elim
  | some b =>
      have hkR : R.lookup? k_x ≠ none := by
        intro hnone
        have hback := hlookup_back k_x b hkR'some
        simp [hnone] at hback
      have hvr_R := h x qt_x k_x hlook hguard hkR
      exact
        varsRegime_transport_active_lookup_back
          (predSat := predSat) (R := R) (R' := R')
          (μ := μ) (ρ := ρcap) (entry := (x, qt_x))
          hlookup_back hguard hkR'some hvr_R

lemma closureCapturedVarsRegime_transport_lookup_back
  {predSat : PredSat} {R R' : Regime} {qt : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  (hlookup_back : ∀ k b, R'.lookup? k = some b → R.lookup? k = some b)
  (h : closureCapturedVarsRegime predSat R qt μ θ v) :
  closureCapturedVarsRegime predSat R' qt μ θ v := by
  cases h with
  | intro hdeep =>
      exact .intro (deepValueQTypProperty_mono
        (fun σcap ρcap ⟨hP, hT⟩ =>
          ⟨capturedVarsRegimeProperty_transport_lookup_back
            (predSat := predSat) (R := R) (R' := R') (μ := μ)
            hlookup_back hP, hT⟩)
        hdeep)

lemma memberVarsRegimeEvidence_transport_lookup_back
  {predSat : PredSat} {R R' : Regime} {μ : Memory}
  (hlookup_back : ∀ k b, R'.lookup? k = some b → R.lookup? k = some b)
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (h : MemberVarsRegimeEvidence predSat R μ σcap ρcap) :
  MemberVarsRegimeEvidence predSat R' μ σcap ρcap := by
  intro y qt_y k_y v_y hlookup_σ hlookup_ρ hguard hkR'
  cases hkR'some : R'.lookup? k_y with
  | none =>
      exact (hkR' hkR'some).elim
  | some b =>
      have hkR : R.lookup? k_y ≠ none := by
        intro hnone
        have hback := hlookup_back k_y b hkR'some
        simp [hnone] at hback
      have hvr_R :
          varsRegime predSat R μ ρcap (y, qt_y) :=
        h y qt_y k_y v_y hlookup_σ hlookup_ρ hguard hkR
      exact
        varsRegime_transport_active_lookup_back
          (predSat := predSat) (R := R) (R' := R')
          (μ := μ) (ρ := ρcap) (entry := (y, qt_y))
          hlookup_back hguard hkR'some hvr_R

lemma memberCvcrEvidence_transport_lookup_back
  {predSat : PredSat} {R R' : Regime} {μ : Memory} {θ : RealizationMap}
  (hlookup_back : ∀ k b, R'.lookup? k = some b → R.lookup? k = some b)
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (h : MemberCvcrEvidence predSat R μ θ σcap ρcap) :
  MemberCvcrEvidence predSat R' μ θ σcap ρcap := by
  intro y qt_y v_y hlookup_σ hlookup_ρ
  exact
    closureCapturedVarsRegime_transport_lookup_back
      (predSat := predSat) (R := R) (R' := R') (μ := μ)
      hlookup_back (h y qt_y v_y hlookup_σ hlookup_ρ)

-- Transport closureCapturedVarsRegime across qt.etyp equality.
lemma closureCapturedVarsRegime_transport_etyp
  {predSat : PredSat} {R : Regime} {qt qt' : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  (hetyp : qt.etyp = qt'.etyp)
  (h : closureCapturedVarsRegime predSat R qt μ θ v) :
  closureCapturedVarsRegime predSat R qt' μ θ v := by
  cases h with
  | intro hdeep =>
      refine .intro ?_
      cases hdeep with
      | nonClosure hv hpe => exact .nonClosure hv hpe
      | closure xp body ρcap σcap st1 st2 p tcls hval hetyp_eq hmem hP hrec =>
          exact .closure xp body ρcap σcap st1 st2 p tcls hval (hetyp ▸ hetyp_eq) hmem hP hrec
      | peClosure xp body pbody ρcap σcap st1 st2 p tcls hval hetyp_eq hpure hmem hP hrec =>
          exact .peClosure xp body pbody ρcap σcap st1 st2 p tcls hval (hetyp ▸ hetyp_eq) hpure hmem hP hrec

-- Weaken closureCapturedVarsRegime when the closure list grows (superset).
-- Used when joining type results: mergeFnTClosures produces a superset.
lemma closureCapturedVarsRegime_weaken_fnTClosures
  {predSat : PredSat} {R : Regime} {μ : Memory} {θ : RealizationMap} {v : Value}
  {st1 st2 : Typ} {p : Poison} {tcls tcls' : List FnTClosure} {poison : Poison} {pred : Predicate}
  (hmem : ∀ tcl, tcl ∈ tcls → tcl ∈ tcls')
  (h : closureCapturedVarsRegime predSat R ⟨ETyp.arrow st1 st2 p tcls, poison, pred⟩ μ θ v) :
  closureCapturedVarsRegime predSat R ⟨ETyp.arrow st1 st2 p tcls', poison, pred⟩ μ θ v := by
  cases h with
  | intro hdeep =>
      refine .intro ?_
      cases hdeep with
      | nonClosure hv hpe => exact .nonClosure hv hpe
      | closure xp body ρcap σcap _st1 _st2 _p tcls_src hval hetyp_eq hmem_src hP hrec =>
          have heq_tcls : tcls_src = tcls := ((ETyp.arrow.injEq ..).mp hetyp_eq |>.2.2.2).symm
          subst heq_tcls
          exact .closure xp body ρcap σcap st1 st2 p tcls' hval rfl (hmem _ hmem_src) hP hrec
      | peClosure _ _ _ _ _ _ _ _ _ _ hetyp_eq_parr _ _ =>
          exfalso
          simp at hetyp_eq_parr

-- Weaken with different inner poison (joinETyps changes p to joinPoison p1 p2).
lemma closureCapturedVarsRegime_weaken_fnTClosures'
  {predSat : PredSat} {R : Regime} {μ : Memory} {θ : RealizationMap} {v : Value}
  {st1 st2 : Typ} {p p' : Poison} {tcls tcls' : List FnTClosure} {poison : Poison} {pred : Predicate}
  (hmem : ∀ tcl, tcl ∈ tcls → tcl ∈ tcls')
  (h : closureCapturedVarsRegime predSat R ⟨ETyp.arrow st1 st2 p tcls, poison, pred⟩ μ θ v) :
  closureCapturedVarsRegime predSat R ⟨ETyp.arrow st1 st2 p' tcls', poison, pred⟩ μ θ v := by
  cases h with
  | intro hdeep =>
      refine .intro ?_
      cases hdeep with
      | nonClosure hv hpe => exact .nonClosure hv hpe
      | closure xp body ρcap σcap _st1 _st2 _p tcls_src hval hetyp_eq hmem_src hP hrec =>
          have heq_tcls : tcls_src = tcls := ((ETyp.arrow.injEq ..).mp hetyp_eq |>.2.2.2).symm
          subst heq_tcls
          exact .closure xp body ρcap σcap st1 st2 p' tcls' hval rfl (hmem _ hmem_src) hP hrec
      | peClosure _ _ _ _ _ _ _ _ _ _ hetyp_eq_parr _ _ =>
          exfalso
          simp at hetyp_eq_parr

-- Analogous for parrow/PFnTClosure.
lemma closureCapturedVarsRegime_weaken_pFnTClosures
  {predSat : PredSat} {R : Regime} {μ : Memory} {θ : RealizationMap} {v : Value}
  {st1 st2 : Typ} {p : Poison} {tcls tcls' : List PFnTClosure} {poison : Poison} {pred : Predicate}
  (hmem : ∀ tcl, tcl ∈ tcls → tcl ∈ tcls')
  (h : closureCapturedVarsRegime predSat R ⟨ETyp.parrow st1 st2 p tcls, poison, pred⟩ μ θ v) :
  closureCapturedVarsRegime predSat R ⟨ETyp.parrow st1 st2 p tcls', poison, pred⟩ μ θ v := by
  cases h with
  | intro hdeep =>
      refine .intro ?_
      cases hdeep with
      | nonClosure hv hpe => exact .nonClosure hv hpe
      | closure _ _ _ _ _ _ _ _ _ hetyp_eq_arr _ _ =>
          exfalso
          simp at hetyp_eq_arr
      | peClosure xp body pbody ρcap σcap _st1 _st2 _p tcls_src hval hetyp_eq hpure hmem_src hP hrec =>
          have heq_tcls : tcls_src = tcls := ((ETyp.parrow.injEq ..).mp hetyp_eq |>.2.2.2).symm
          subst heq_tcls
          exact .peClosure xp body pbody ρcap σcap st1 st2 p tcls' hval rfl hpure (hmem _ hmem_src) hP hrec

-- Weaken parrow with different inner poison (joinETyps changes p).
lemma closureCapturedVarsRegime_weaken_pFnTClosures'
  {predSat : PredSat} {R : Regime} {μ : Memory} {θ : RealizationMap} {v : Value}
  {st1 st2 : Typ} {p p' : Poison} {tcls tcls' : List PFnTClosure} {poison : Poison} {pred : Predicate}
  (hmem : ∀ tcl, tcl ∈ tcls → tcl ∈ tcls')
  (h : closureCapturedVarsRegime predSat R ⟨ETyp.parrow st1 st2 p tcls, poison, pred⟩ μ θ v) :
  closureCapturedVarsRegime predSat R ⟨ETyp.parrow st1 st2 p' tcls', poison, pred⟩ μ θ v := by
  cases h with
  | intro hdeep =>
      refine .intro ?_
      cases hdeep with
      | nonClosure hv hpe => exact .nonClosure hv hpe
      | closure _ _ _ _ _ _ _ _ _ hetyp_eq_arr _ _ =>
          exfalso
          simp at hetyp_eq_arr
      | peClosure xp body pbody ρcap σcap _st1 _st2 _p tcls_src hval hetyp_eq hpure hmem_src hP hrec =>
          have heq_tcls : tcls_src = tcls := ((ETyp.parrow.injEq ..).mp hetyp_eq |>.2.2.2).symm
          subst heq_tcls
          exact .peClosure xp body pbody ρcap σcap st1 st2 p' tcls' hval rfl hpure (hmem _ hmem_src) hP hrec

-- Transport closureCapturedVarsRegime across qt.pred equality.
-- Since the new definition is indexed by qt.etyp, we need an additional
-- etyp equality (defaults to rfl for the common case where only pred changes).
lemma closureCapturedVarsRegime_transport_pred
  {predSat : PredSat} {R : Regime} {qt qt' : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  (_hpred : qt.pred = qt'.pred)
  (h : closureCapturedVarsRegime predSat R qt μ θ v)
  (hetyp : qt.etyp = qt'.etyp := by rfl) :
  closureCapturedVarsRegime predSat R qt' μ θ v :=
  closureCapturedVarsRegime_transport_etyp hetyp h

-- When Regime.monotoneStep R R', valueConsistentWithRegime for R implies for R'
-- (R' has fewer entries, so fewer constraints).
lemma valueConsistentWithRegime_monotone
  {predSat : PredSat} {R R' : Regime} {qt : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  (h_mono : Regime.monotoneStep R R')
  (h : valueConsistentWithRegime predSat R qt μ θ v) :
  valueConsistentWithRegime predSat R' qt μ θ v := by
  cases h with
  | noTag htag hcap =>
      exact valueConsistentWithRegime.noTag htag (closureCapturedVarsRegime_monotone h_mono hcap)
  | guardOnly_ok k hgo hcap =>
      exact valueConsistentWithRegime.guardOnly_ok k hgo (closureCapturedVarsRegime_monotone h_mono hcap)
  | notInRegime k htag hknone hcap =>
      have h' : R'.lookup? k = none := by
        by_contra hneq
        exact h_mono.2.2 k hneq hknone
      exact valueConsistentWithRegime.notInRegime k htag h' (closureCapturedVarsRegime_monotone h_mono hcap)
  | inRegimeTrue k htag hktrue hholds hcap =>
      have hcap' := closureCapturedVarsRegime_monotone h_mono hcap
      have hR' := h_mono.2.1 k true hktrue
      cases hR' with
      | inl hk' =>
          exact valueConsistentWithRegime.inRegimeTrue k htag hk' hholds hcap'
      | inr hk'none =>
          exact valueConsistentWithRegime.notInRegime k htag hk'none hcap'
  | inRegimeFalse k htag hkfalse hnot hcap =>
      have hcap' := closureCapturedVarsRegime_monotone h_mono hcap
      have hR' := h_mono.2.1 k false hkfalse
      cases hR' with
      | inl hk' =>
          exact valueConsistentWithRegime.inRegimeFalse k htag hk' hnot hcap'
      | inr hk'none =>
          exact valueConsistentWithRegime.notInRegime k htag hk'none hcap'

-- Extract closureCapturedVarsRegime evidence from valueConsistentWithRegime.
lemma valueConsistentWithRegime_closureCapturedVarsRegime
  {predSat : PredSat} {R : Regime} {qt : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  (h : valueConsistentWithRegime predSat R qt μ θ v) :
  closureCapturedVarsRegime predSat R qt μ θ v := by
  cases h with
  | noTag _ hcap => exact hcap
  | guardOnly_ok _k _ hcap => exact hcap
  | notInRegime _k _ _ hcap => exact hcap
  | inRegimeTrue _k _ _ _ hcap => exact hcap
  | inRegimeFalse _k _ _ _ hcap => exact hcap

-- For guard-closure predicates, `valueConsistentWithRegime` determines the same
-- predicate-consistency obligation needed by `varsRegime.withPred_ok`.
lemma valueConsistentWithRegime_guardClosure_consistency
  {predSat : PredSat} {R : Regime} {qt : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  {k : Tag} {arg_name : Name} {pred_body : PExpr} {var_env : CapturedVarEnv} {b : Bool}
  (hvalc : valueConsistentWithRegime predSat R qt μ θ v)
  (hpred : qt.pred = Predicate.guardClosure k arg_name pred_body var_env)
  (hreg : R.lookup? k = some b) :
  (b = true → qtypPredHolds predSat qt μ v) ∧
  (b = false → ¬ qtypPredHolds predSat qt μ v) := by
  cases hvalc with
  | noTag htag _ =>
      have : qtypGuardTag qt = some k := by
        simp [qtypGuardTag, hpred]
      simp [this] at htag
  | guardOnly_ok k' hgo _ =>
      simp [hpred] at hgo
  | notInRegime k' htag hnone _ =>
      have hk_eq : k' = k := by
        have : some k' = some k := by
          calc
            some k' = qtypGuardTag qt := by simp [htag]
            _ = some k := by simp [qtypGuardTag, hpred]
        exact Option.some.inj this
      have : R.lookup? k = none := by simpa [hk_eq] using hnone
      simp [this] at hreg
  | inRegimeTrue k' htag hk hholds _ =>
      have hk_eq : k' = k := by
        have : some k' = some k := by
          calc
            some k' = qtypGuardTag qt := by simp [htag]
            _ = some k := by simp [qtypGuardTag, hpred]
        exact Option.some.inj this
      have hk_true : R.lookup? k = some true := by simpa [hk_eq] using hk
      constructor
      · intro hbtrue
        have hb_eq_true : b = true := by
          have : some b = some true := by
            calc
              some b = R.lookup? k := by symm; exact hreg
              _ = some true := hk_true
          exact Option.some.inj this
        subst hb_eq_true
        exact hholds
      · intro hbfalse
        have hb_eq_true : b = true := by
          have : some b = some true := by
            calc
              some b = R.lookup? k := by symm; exact hreg
              _ = some true := hk_true
          exact Option.some.inj this
        have : true = false := hb_eq_true.symm.trans hbfalse
        cases this
  | inRegimeFalse k' htag hk hnot _ =>
      have hk_eq : k' = k := by
        have : some k' = some k := by
          calc
            some k' = qtypGuardTag qt := by simp [htag]
            _ = some k := by simp [qtypGuardTag, hpred]
        exact Option.some.inj this
      have hk_false : R.lookup? k = some false := by simpa [hk_eq] using hk
      constructor
      · intro hbtrue
        have hb_eq_false : b = false := by
          have : some b = some false := by
            calc
              some b = R.lookup? k := by symm; exact hreg
              _ = some false := hk_false
          exact Option.some.inj this
        have : false = true := hb_eq_false.symm.trans hbtrue
        cases this
      · intro hbfalse
        have hb_eq_false : b = false := by
          have : some b = some false := by
            calc
              some b = R.lookup? k := by symm; exact hreg
              _ = some false := hk_false
          exact Option.some.inj this
        subst hb_eq_false
        exact hnot

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

-- Transport `varsRegime` across a memory change when predicate truth is preserved.
lemma varsRegime_transport_predHolds
  {predSat : PredSat} {R : Regime} {μ μ' : Memory} {ρ : VarEnv} {entry : Name × QTyp}
  (hpred_compat : ∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ v ↔ qtypPredHolds predSat qt μ' v)
  (h : varsRegime predSat R μ ρ entry) :
  varsRegime predSat R μ' ρ entry := by
  cases h with
  | noPred_ok hnp =>
      exact varsRegime.noPred_ok entry hnp
  | guardOnly_ok k hgo =>
      exact varsRegime.guardOnly_ok entry k hgo
  | withPred_ok k arg_name pred_body var_env v b hclos hreg hvar hcons =>
      exact varsRegime.withPred_ok entry k arg_name pred_body var_env v b hclos hreg hvar
        ⟨fun hbtrue => (hpred_compat _ v).1 (hcons.1 hbtrue),
         fun hbfalse hholds => hcons.2 hbfalse ((hpred_compat _ v).2 hholds)⟩

lemma memberVarsRegimeEvidence_monotone
  {predSat : PredSat} {R R' : Regime} {μ : Memory}
  (h_mono : Regime.monotoneStep R R')
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (h : MemberVarsRegimeEvidence predSat R μ σcap ρcap) :
  MemberVarsRegimeEvidence predSat R' μ σcap ρcap := by
  intro y qt_y k_y v_y hlookup_σ hlookup_ρ hguard hkR'
  have hkR : R.lookup? k_y ≠ none := fun hnone => h_mono.2.2 k_y hkR' hnone
  have hvr_R :
      varsRegime predSat R μ ρcap (y, qt_y) :=
    h y qt_y k_y v_y hlookup_σ hlookup_ρ hguard hkR
  cases hRk : R.lookup? k_y with
  | none =>
      exact (hkR hRk).elim
  | some b =>
      cases h_mono.2.1 k_y b hRk with
      | inl hkR'_eq =>
          exact varsRegime_monotone h_mono hguard hRk hkR'_eq hvr_R
      | inr hkR'_none =>
          exact (hkR' hkR'_none).elim

lemma memberVarsRegimeEvidence_transport_μ
  {predSat : PredSat} {R : Regime} {μ μ' : Memory}
  (hpred_compat : ∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ v ↔ qtypPredHolds predSat qt μ' v)
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (h : MemberVarsRegimeEvidence predSat R μ σcap ρcap) :
  MemberVarsRegimeEvidence predSat R μ' σcap ρcap := by
  intro y qt_y k_y v_y hlookup_σ hlookup_ρ hguard hkR
  exact
    varsRegime_transport_predHolds hpred_compat
      (h y qt_y k_y v_y hlookup_σ hlookup_ρ hguard hkR)

-- Transport capturedVarsRegimeProperty across memory change given a predicate iff.
lemma capturedVarsRegimeProperty_transport_predHolds
  {predSat : PredSat} {R : Regime} {μ μ' : Memory}
  (hpred_compat : ∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ v ↔ qtypPredHolds predSat qt μ' v)
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (h : capturedVarsRegimeProperty predSat R μ σcap ρcap) :
  capturedVarsRegimeProperty predSat R μ' σcap ρcap := by
  intro x qt_x k_x hlook hguard hkR
  have hvr := h x qt_x k_x hlook hguard hkR
  cases hvr with
  | noPred_ok hnp => exact varsRegime.noPred_ok _ hnp
  | guardOnly_ok k hgo => exact varsRegime.guardOnly_ok _ k hgo
  | withPred_ok k arg_name pred_body var_env v b hclos hreg hvar hconsist =>
      exact varsRegime.withPred_ok _ k arg_name pred_body var_env v b hclos hreg hvar
        ⟨fun hbtrue => (hpred_compat _ v).1 (hconsist.1 hbtrue),
         fun hbfalse hholds => hconsist.2 hbfalse ((hpred_compat _ v).2 hholds)⟩

-- Transport closureCapturedVarsRegime across memory change given a predicate iff.
lemma closureCapturedVarsRegime_transport_μ
  {predSat : PredSat} {R : Regime} {qt : QTyp} {μ μ' : Memory} {θ : RealizationMap} {v : Value}
  (hpred_compat : ∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ v ↔ qtypPredHolds predSat qt μ' v)
  (h : closureCapturedVarsRegime predSat R qt μ θ v) :
  closureCapturedVarsRegime predSat R qt μ' θ v := by
  cases h with
  | intro hdeep =>
      exact .intro (deepValueQTypProperty_mono
        (fun σcap ρcap ⟨hP, hT⟩ => ⟨capturedVarsRegimeProperty_transport_predHolds hpred_compat hP, hT⟩)
        hdeep)

-- Monotonicity of valueHasETyp under θ extension.
-- Moved before transport lemmas so they can use it.
lemma valueHasETyp_extends'
  {θ₀ θ₁ : RealizationMap} {v : Value} {t : ETyp} :
  θ₀.extendsMap θ₁ →
  valueHasETyp θ₀ v t →
  valueHasETyp θ₁ v t := by
  intro hExt hval
  induction hval generalizing θ₁ with
  | num n => exact valueHasETyp.num n
  | bool b => exact valueHasETyp.bool b
  | unit => exact valueHasETyp.unit
  | str s => exact valueHasETyp.str s
  | loc hlookup hin => exact valueHasETyp.loc (hExt _ _ hlookup) hin
  | closure htcl henv hcover ih =>
      refine valueHasETyp.closure (htcl := htcl) (hcover := hcover) ?_
      intro y qt v hlookupT hlookupV
      exact ih y qt v hlookupT hlookupV hExt
  | peClosure hpure htcl henv hcover ih =>
      refine valueHasETyp.peClosure (hpure := hpure) (htcl := htcl) (hcover := hcover) ?_
      intro y qt v hlookupT hlookupV
      exact ih y qt v hlookupT hlookupV hExt

-- Transport closureCapturedVarsRegime across both memory and θ (map extension).
-- The regime property is insensitive to θ; the typing property is monotone
-- under θ extension via valueHasETyp_extends'.
lemma closureCapturedVarsRegime_transport_μ_θ
  {predSat : PredSat} {R : Regime} {qt : QTyp} {μ μ' : Memory} {θ θ' : RealizationMap} {v : Value}
  (hpred_compat : ∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ v ↔ qtypPredHolds predSat qt μ' v)
  (hθ : θ.extendsMap θ')
  (h : closureCapturedVarsRegime predSat R qt μ θ v) :
  closureCapturedVarsRegime predSat R qt μ' θ' v := by
  cases h with
  | intro hdeep =>
      exact .intro (deepValueQTypProperty_mono
        (fun σcap ρcap ⟨hP, hnd, hcover, htyp⟩ =>
          ⟨capturedVarsRegimeProperty_transport_predHolds hpred_compat hP,
           hnd, hcover,
           fun y qt_y v_y hσ hρ => valueHasETyp_extends' hθ (htyp y qt_y v_y hσ hρ)⟩)
        hdeep)

lemma memberCvcrEvidence_monotone
  {predSat : PredSat} {R R' : Regime} {μ : Memory} {θ : RealizationMap}
  (h_mono : Regime.monotoneStep R R')
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (h : MemberCvcrEvidence predSat R μ θ σcap ρcap) :
  MemberCvcrEvidence predSat R' μ θ σcap ρcap := by
  intro y qt_y v_y hlookup_σ hlookup_ρ
  exact
    closureCapturedVarsRegime_monotone h_mono
      (h y qt_y v_y hlookup_σ hlookup_ρ)

lemma memberCvcrEvidence_transport_μ
  {predSat : PredSat} {R : Regime} {μ μ' : Memory} {θ : RealizationMap}
  (hpred_compat : ∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ v ↔ qtypPredHolds predSat qt μ' v)
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (h : MemberCvcrEvidence predSat R μ θ σcap ρcap) :
  MemberCvcrEvidence predSat R μ' θ σcap ρcap := by
  intro y qt_y v_y hlookup_σ hlookup_ρ
  exact
    closureCapturedVarsRegime_transport_μ hpred_compat
      (h y qt_y v_y hlookup_σ hlookup_ρ)

-- Transport MemberCvcrEvidence across both μ and θ (extends).
-- The θ transport requires recursing through deepValueQTypProperty to update
-- capturedVarsTypingProperty via valueHasETyp_extends at every nesting level.
lemma memberCvcrEvidence_transport_μ_θ
  {predSat : PredSat} {R : Regime} {μ μ' : Memory} {θ θ' : RealizationMap}
  (hpred_compat : ∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ v ↔ qtypPredHolds predSat qt μ' v)
  (hθ : θ.extendsMap θ')
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (h : MemberCvcrEvidence predSat R μ θ σcap ρcap) :
  MemberCvcrEvidence predSat R μ' θ' σcap ρcap := by
  intro y qt_y v_y hlookup_σ hlookup_ρ
  exact closureCapturedVarsRegime_transport_μ_θ hpred_compat hθ
    (h y qt_y v_y hlookup_σ hlookup_ρ)

-- Transport with explicit closureCapturedVarsRegime transport (used when etyp may differ, e.g. joinETyps).
lemma valueConsistentWithRegime_transport_pred'
  {predSat : PredSat} {R : Regime} {qt qt' : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  (hpred : qt.pred = qt'.pred)
  (hcap_tr : closureCapturedVarsRegime predSat R qt μ θ v → closureCapturedVarsRegime predSat R qt' μ θ v) :
  valueConsistentWithRegime predSat R qt μ θ v →
  valueConsistentWithRegime predSat R qt' μ θ v := by
  intro h
  cases h with
  | noTag htag hcap =>
      refine valueConsistentWithRegime.noTag (predSat := predSat) (R := R) (qt := qt') ?_
        (hcap_tr hcap)
      have hEq := qtypGuardTag_of_pred_eq (qt := qt) (qt' := qt') hpred
      simpa [hEq.symm] using htag
  | guardOnly_ok k hgo hcap =>
      refine valueConsistentWithRegime.guardOnly_ok (predSat := predSat) (R := R)
        (qt := qt') (μ := μ) (v := v) k ?_ (hcap_tr hcap)
      calc qt'.pred = qt.pred := by simp [hpred]
        _ = Predicate.guardOnly k := hgo
  | notInRegime k htag hknone hcap =>
      refine valueConsistentWithRegime.notInRegime (predSat := predSat) (R := R)
        (qt := qt') (μ := μ) (v := v) k ?_ hknone (hcap_tr hcap)
      have hEq := qtypGuardTag_of_pred_eq (qt := qt) (qt' := qt') hpred
      simpa [hEq.symm] using htag
  | inRegimeTrue k htag hktrue hholds hcap =>
      refine valueConsistentWithRegime.inRegimeTrue (predSat := predSat) (R := R)
        (qt := qt') (μ := μ) (v := v) k ?_ hktrue ?_ (hcap_tr hcap)
      · have hEq := qtypGuardTag_of_pred_eq (qt := qt) (qt' := qt') hpred
        simpa [hEq.symm] using htag
      · exact qtypPredHolds_transport_pred (predSat := predSat) (qt := qt) (qt' := qt')
          (μ := μ) (v := v) hpred hholds
  | inRegimeFalse k htag hkfalse hnot hcap =>
      refine valueConsistentWithRegime.inRegimeFalse (predSat := predSat) (R := R)
        (qt := qt') (μ := μ) (v := v) k ?_ hkfalse ?_ (hcap_tr hcap)
      · have hEq := qtypGuardTag_of_pred_eq (qt := qt) (qt' := qt') hpred
        simpa [hEq.symm] using htag
      · exact qtypPredHolds_transport_pred_not (predSat := predSat) (qt := qt) (qt' := qt')
          (μ := μ) (v := v) hpred hnot

lemma valueConsistentWithRegime_transport_pred
  {predSat : PredSat} {R : Regime} {qt qt' : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  (hpred : qt.pred = qt'.pred)
  (hetyp : qt.etyp = qt'.etyp := by rfl) :
  valueConsistentWithRegime predSat R qt μ θ v →
  valueConsistentWithRegime predSat R qt' μ θ v := by
  intro h
  have hcap_tr : ∀ hcap : closureCapturedVarsRegime predSat R qt μ θ v,
      closureCapturedVarsRegime predSat R qt' μ θ v :=
    fun hcap => closureCapturedVarsRegime_transport_etyp hetyp hcap
  cases h with
  | noTag htag hcap =>
      refine valueConsistentWithRegime.noTag (predSat := predSat) (R := R) (qt := qt') ?_
        (hcap_tr hcap)
      have hEq := qtypGuardTag_of_pred_eq (qt := qt) (qt' := qt') hpred
      simpa [hEq.symm] using htag
  | guardOnly_ok k hgo hcap =>
      refine valueConsistentWithRegime.guardOnly_ok (predSat := predSat) (R := R)
        (qt := qt') (μ := μ) (v := v) k ?_ (hcap_tr hcap)
      calc qt'.pred = qt.pred := by simp [hpred]
        _ = Predicate.guardOnly k := hgo
  | notInRegime k htag hknone hcap =>
      refine valueConsistentWithRegime.notInRegime (predSat := predSat) (R := R)
        (qt := qt') (μ := μ) (v := v) k ?_ hknone (hcap_tr hcap)
      have hEq := qtypGuardTag_of_pred_eq (qt := qt) (qt' := qt') hpred
      simpa [hEq.symm] using htag
  | inRegimeTrue k htag hktrue hholds hcap =>
      refine valueConsistentWithRegime.inRegimeTrue (predSat := predSat) (R := R)
        (qt := qt') (μ := μ) (v := v) k ?_ hktrue ?_ (hcap_tr hcap)
      · have hEq := qtypGuardTag_of_pred_eq (qt := qt) (qt' := qt') hpred
        simpa [hEq.symm] using htag
      · exact qtypPredHolds_transport_pred (predSat := predSat) (qt := qt) (qt' := qt')
          (μ := μ) (v := v) hpred hholds
  | inRegimeFalse k htag hkfalse hnot hcap =>
      refine valueConsistentWithRegime.inRegimeFalse (predSat := predSat) (R := R)
        (qt := qt') (μ := μ) (v := v) k ?_ hkfalse ?_ (hcap_tr hcap)
      · have hEq := qtypGuardTag_of_pred_eq (qt := qt) (qt' := qt') hpred
        simpa [hEq.symm] using htag
      · exact qtypPredHolds_transport_pred_not (predSat := predSat) (qt := qt) (qt' := qt')
          (μ := μ) (v := v) hpred hnot

-- Helper: when valueHasETyp holds and etyp is not a function type, the value
-- is neither a closure nor a peClosure.
lemma nonClosure_of_nonFunctionType
  {θ : RealizationMap} {v : Value} {etyp : ETyp}
  (hvet : valueHasETyp θ v etyp)
  (hnotfun : etyp.isFunctionType = false) :
  (∀ xp bd rc, v ≠ Value.closure xp bd rc) ∧
  (∀ xp bd rc, v ≠ Value.peClosure xp bd rc) := by
  constructor
  · intro xp bd rc h; subst h
    cases hvet with
    | closure => simp [ETyp.isFunctionType, ETyp.isArrow] at hnotfun
  · intro xp bd rc h; subst h
    cases hvet with
    | peClosure => simp [ETyp.isFunctionType, ETyp.isParrow] at hnotfun

-- Helper: construct closureCapturedVarsRegime for non-closure values using
-- typeHasETyp evidence.
lemma closureCapturedVarsRegime_nonClosure_of_nonFunctionType
  {predSat : PredSat} {R : Regime} {qt : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  (hvet : valueHasETyp θ v qt.etyp)
  (hnotfun : qt.etyp.isFunctionType = false) :
  closureCapturedVarsRegime predSat R qt μ θ v :=
  let ⟨hnc, hnpe⟩ := nonClosure_of_nonFunctionType hvet hnotfun
  .intro (.nonClosure hnc hnpe)

lemma ret_eq_of_agreeValueUnder_nonref
  {predSat : PredSat} {R : Regime} {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
  {qt : QTyp} {o₀ o₁ : Value} :
  (¬ ∃ ls, qt.etyp = ETyp.ref ls) →
  qt.etyp.isFunctionType = false →
  qt.poison = false →
  agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ →
  o₀ = o₁ := by
  intro hnotref hnotfun hpoison hret_agree
  cases hret_agree with
  | clean_eq_nonref_nonarrow _ _ _ hval => exact hval
  | withPred_true_eq _ _ _ _ _ hval => exact hval
  | clean_internal_arrow _ hetyp _ _ _ _ _ _ _ =>
      exfalso
      simp [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hnotfun
  | dirty_internal_arrow _ hisArrow =>
      exfalso
      have hfun : qt.etyp.isFunctionType = true := by
        simp only [ETyp.isFunctionType, Bool.or_eq_true]
        left
        exact hisArrow
      rw [hfun] at hnotfun
      cases hnotfun
  | clean_internal_parrow _ hetyp _ _ _ _ _ _ _ =>
      exfalso
      simp [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hnotfun
  | dirty_internal_parrow _ hisParrow =>
      exfalso
      have hfun : qt.etyp.isFunctionType = true := by
        simp only [ETyp.isFunctionType, Bool.or_eq_true]
        right
        exact hisParrow
      rw [hfun] at hnotfun
      cases hnotfun
  | clean_ref _ hetyp _ _ _ _ _ =>
      exfalso
      exact hnotref ⟨_, hetyp⟩
  | withPred_true_ref _ _ _ hetyp _ _ _ _ =>
      exfalso
      exact hnotref ⟨_, hetyp⟩

lemma agreeValueUnder_nonref_eq_of_clean
  {predSat : PredSat} {R : Regime} {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
  {qt : QTyp} {o₀ o₁ : Value} :
  qtypCleanUnder R qt →
  (¬ ∃ ls, qt.etyp = ETyp.ref ls) →
  qt.etyp.isFunctionType = false →
  agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ →
  o₀ = o₁ := by
  intro hclean hnotref hnotfun hagree
  cases hagree with
  | clean_eq_nonref_nonarrow _ _ _ hval => exact hval
  | withPred_true_eq _ _ _ _ _ hval => exact hval
  | clean_internal_arrow _ hetyp _ _ _ _ _ _ _ =>
      exfalso
      simp [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hnotfun
  | dirty_internal_arrow _ hisArrow =>
      exfalso
      have hfun : qt.etyp.isFunctionType = true := by
        simp only [ETyp.isFunctionType, Bool.or_eq_true]
        left
        exact hisArrow
      rw [hfun] at hnotfun
      cases hnotfun
  | clean_internal_parrow _ hetyp _ _ _ _ _ _ _ =>
      exfalso
      simp [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hnotfun
  | dirty_internal_parrow _ hisParrow =>
      exfalso
      have hfun : qt.etyp.isFunctionType = true := by
        simp only [ETyp.isFunctionType, Bool.or_eq_true]
        right
        exact hisParrow
      rw [hfun] at hnotfun
      cases hnotfun
  | clean_ref _ hetyp _ _ _ _ _ =>
      exfalso
      exact hnotref ⟨_, hetyp⟩
  | withPred_true_ref _ _ _ hetyp _ _ _ _ =>
      exfalso
      exact hnotref ⟨_, hetyp⟩

lemma agreeValueUnder_transport_clean
  {predSat : PredSat} {R : Regime} {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
  {qt qt2 : QTyp} {o₀ o₁ : Value} :
  qtypCleanUnder R qt →
  qt.etyp = qt2.etyp →
  (qt.poison = false → qt2.poison = false) →
  agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt2 o₀ o₁ →
  agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ := by
  intro hclean hetyp hpoison_imp hagree
  cases hclean with
  | clean hpoison =>
      have hpoison2 : qt2.poison = false := hpoison_imp hpoison
      cases hagree with
      | clean_eq_nonref_nonarrow _ hnotfun hnotref hEq =>
          have hnotfun' : qt.etyp.isFunctionType = false := by
            simpa [hetyp.symm] using hnotfun
          have hnotref' : ¬ ∃ ls, qt.etyp = ETyp.ref ls := by
            intro ⟨ls, h⟩
            apply hnotref
            exact ⟨ls, by simpa [hetyp] using h⟩
          exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison hnotfun' hnotref' hEq
      | withPred_true_eq _ _ _ hnotfun hnotref hEq =>
          have hnotfun' : qt.etyp.isFunctionType = false := by
            simpa [hetyp.symm] using hnotfun
          have hnotref' : ¬ ∃ ls, qt.etyp = ETyp.ref ls := by
            intro ⟨ls, h⟩
            apply hnotref
            exact ⟨ls, by simpa [hetyp] using h⟩
          exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison hnotfun' hnotref' hEq
      | clean_internal_arrow hclean_int hetyp1 htcl hmatch hcap
          hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ hv₁ hv₂ =>
          have hetyp' := hetyp.trans hetyp1
          -- Need to show internal poison is clean for qt
          -- qt.poison = false (from hpoison), qt.etyp = qt2.etyp (from hetyp)
          -- qt2 has clean_internal_arrow, so its internal poison is clean
          -- Since qt.etyp = qt2.etyp, qt's internal poison is also clean
          have hclean_int_qt : internalPoisonClean qt := by
            simp only [internalPoisonClean]
            simp only [hetyp]
            exact hclean_int
          exact agreeValueUnder.clean_internal_arrow hclean_int_qt hetyp' htcl hmatch hcap
            hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ hv₁ hv₂
      | dirty_internal_arrow hdirty_int hisArrow htyp1_qt2 htyp2_qt2 =>
          -- qt2 has dirty internal, but qt.poison = false (hpoison)
          -- We need to construct agreement for qt
          -- Since qt.etyp = qt2.etyp and qt2.etyp.isArrow = true, qt.etyp.isArrow = true
          have hisArrow_qt : qt.etyp.isArrow = true := by
            rw [hetyp]; exact hisArrow
          -- But we need to decide: is qt's internal poison clean or dirty?
          -- qt2's internal is dirty (hdirty_int), and qt.etyp = qt2.etyp, so qt's internal is also dirty
          have hdirty_int_qt : ¬internalPoisonClean qt := by
            simp only [internalPoisonClean]
            simp only [hetyp]
            exact hdirty_int
          -- Transport typing proofs from qt2.etyp to qt.etyp
          have htyp1_qt : valueHasETyp θ₀ o₀ qt.etyp := by
            rw [hetyp]; exact htyp1_qt2
          have htyp2_qt : valueHasETyp θ₁ o₁ qt.etyp := by
            rw [hetyp]; exact htyp2_qt2
          exact agreeValueUnder.dirty_internal_arrow hdirty_int_qt hisArrow_qt htyp1_qt htyp2_qt
      | clean_internal_parrow hclean_int hetyp1 htcl hmatch hcap
          hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ hv₁ hv₂ =>
          have hetyp' := hetyp.trans hetyp1
          have hclean_int_qt : internalPoisonClean qt := by
            simp only [internalPoisonClean]
            simp only [hetyp]
            exact hclean_int
          exact agreeValueUnder.clean_internal_parrow hclean_int_qt hetyp' htcl hmatch hcap
            hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ hv₁ hv₂
      | dirty_internal_parrow hdirty_int hisParrow htyp1_qt2 htyp2_qt2 =>
          have hisParrow_qt : qt.etyp.isParrow = true := by
            rw [hetyp]; exact hisParrow
          have hdirty_int_qt : ¬internalPoisonClean qt := by
            simp only [internalPoisonClean]
            simp only [hetyp]
            exact hdirty_int
          -- Transport typing proofs from qt2.etyp to qt.etyp
          have htyp1_qt : valueHasETyp θ₀ o₀ qt.etyp := by
            rw [hetyp]; exact htyp1_qt2
          have htyp2_qt : valueHasETyp θ₁ o₁ qt.etyp := by
            rw [hetyp]; exact htyp2_qt2
          exact agreeValueUnder.dirty_internal_parrow hdirty_int_qt hisParrow_qt htyp1_qt htyp2_qt
      | clean_ref _hpoison2 hetyp1 hlookup1 hin hv1 hlookup2 hv2 =>
          exact agreeValueUnder.clean_ref hpoison (hetyp.trans hetyp1) hlookup1 hin hv1 hlookup2 hv2
      | withPred_true_ref _k _htag _hregime hetyp1 hlookup1 hin hv1 hlookup2 hv2 =>
          exact agreeValueUnder.clean_ref hpoison (hetyp.trans hetyp1) hlookup1 hin hv1 hlookup2 hv2
  | guard k htag hreg _ =>
      cases hagree with
      | clean_eq_nonref_nonarrow _ hnotfun hnotref hEq =>
          have hnotfun' : qt.etyp.isFunctionType = false := by
            simpa [hetyp.symm] using hnotfun
          have hnotref' : ¬ ∃ ls, qt.etyp = ETyp.ref ls := by
            intro ⟨ls, h⟩
            apply hnotref
            exact ⟨ls, by simpa [hetyp] using h⟩
          exact agreeValueUnder.withPred_true_eq k htag hreg hnotfun' hnotref' hEq
      | withPred_true_eq _ _ _ hnotfun hnotref hEq =>
          have hnotfun' : qt.etyp.isFunctionType = false := by
            simpa [hetyp.symm] using hnotfun
          have hnotref' : ¬ ∃ ls, qt.etyp = ETyp.ref ls := by
            intro ⟨ls, h⟩
            apply hnotref
            exact ⟨ls, by simpa [hetyp] using h⟩
          exact agreeValueUnder.withPred_true_eq k htag hreg hnotfun' hnotref' hEq
      | clean_internal_arrow hclean_int hetyp1 htcl hmatch hcap
          hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ hv₁ hv₂ =>
          have hetyp' := hetyp.trans hetyp1
          have hclean_int_qt : internalPoisonClean qt := by
            simp only [internalPoisonClean]
            simp only [hetyp]
            exact hclean_int
          exact agreeValueUnder.clean_internal_arrow hclean_int_qt hetyp' htcl hmatch hcap
            hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ hv₁ hv₂
      | dirty_internal_arrow hdirty_int hisArrow htyp1_qt2 htyp2_qt2 =>
          have hisArrow_qt : qt.etyp.isArrow = true := by
            rw [hetyp]; exact hisArrow
          have hdirty_int_qt : ¬internalPoisonClean qt := by
            simp only [internalPoisonClean]
            simp only [hetyp]
            exact hdirty_int
          -- Transport typing proofs from qt2.etyp to qt.etyp
          have htyp1_qt : valueHasETyp θ₀ o₀ qt.etyp := by
            rw [hetyp]; exact htyp1_qt2
          have htyp2_qt : valueHasETyp θ₁ o₁ qt.etyp := by
            rw [hetyp]; exact htyp2_qt2
          exact agreeValueUnder.dirty_internal_arrow hdirty_int_qt hisArrow_qt htyp1_qt htyp2_qt
      | clean_internal_parrow hclean_int hetyp1 htcl hmatch hcap
          hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ hv₁ hv₂ =>
          have hetyp' := hetyp.trans hetyp1
          have hclean_int_qt : internalPoisonClean qt := by
            simp only [internalPoisonClean]
            simp only [hetyp]
            exact hclean_int
          exact agreeValueUnder.clean_internal_parrow hclean_int_qt hetyp' htcl hmatch hcap
            hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ hv₁ hv₂
      | dirty_internal_parrow hdirty_int hisParrow htyp1_qt2 htyp2_qt2 =>
          have hisParrow_qt : qt.etyp.isParrow = true := by
            rw [hetyp]; exact hisParrow
          have hdirty_int_qt : ¬internalPoisonClean qt := by
            simp only [internalPoisonClean]
            simp only [hetyp]
            exact hdirty_int
          -- Transport typing proofs from qt2.etyp to qt.etyp
          have htyp1_qt : valueHasETyp θ₀ o₀ qt.etyp := by
            rw [hetyp]; exact htyp1_qt2
          have htyp2_qt : valueHasETyp θ₁ o₁ qt.etyp := by
            rw [hetyp]; exact htyp2_qt2
          exact agreeValueUnder.dirty_internal_parrow hdirty_int_qt hisParrow_qt htyp1_qt htyp2_qt
      | clean_ref _hpoison2 hetyp1 hlookup1 hin hv1 hlookup2 hv2 =>
          exact agreeValueUnder.withPred_true_ref k htag hreg (hetyp.trans hetyp1) hlookup1 hin hv1 hlookup2 hv2
      | withPred_true_ref _k2 _htag2 _hregime2 hetyp1 hlookup1 hin hv1 hlookup2 hv2 =>
          exact agreeValueUnder.withPred_true_ref k htag hreg (hetyp.trans hetyp1) hlookup1 hin hv1 hlookup2 hv2

lemma valueHasETyp_num_etyp {θ : RealizationMap} {n : Int} {t : ETyp} :
  valueHasETyp θ (Value.num n) t → t = ETyp.int := by
  intro h
  cases h
  rfl

lemma typecheckDeref_etyp_int
  (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckDeref .ioFree ctx e fuel = .ok res → res.qualType.etyp = ETyp.int := by
  intro h_typecheck
  cases fuel with
  | zero =>
      unfold typecheckDeref at h_typecheck
      simp at h_typecheck
  | succ fuel' =>
      unfold typecheckDeref at h_typecheck
      simp at h_typecheck
      simp [bind, Except.bind] at h_typecheck
      cases h_tc1 : typecheckExpr .ioFree ctx e fuel' with
      | error err =>
          simp [h_tc1] at h_typecheck
      | ok result1 =>
          simp [h_tc1] at h_typecheck
          cases h_qt : result1.qualType with
          | mk etyp poisonRef predRef =>
              rw [h_qt] at h_typecheck
              simp at h_typecheck
              cases etyp <;> simp at h_typecheck
              -- only ref case can succeed; in ref branch split on ls.isEmpty
              rename_i ls
              split at h_typecheck
              · -- ls.isEmpty = true: typecheck throws, contradicts .ok res
                cases h_typecheck
              · -- ls.isEmpty = false: foldM runs, then if poisonRef / else match mergedPred
                cases h_fold : LocSet.foldM (m := Except String) ls (false, none)
                  (fun (accPoison, accPred?) l => do
                    match result1.memEnv'.lookup l with
                    | some qt =>
                        pure (joinPoison accPoison qt.poison,
                          match accPred? with
                          | none => some qt.pred
                          | some p => some (joinPredicates p qt.pred))
                    | none => throw (toString "Location " ++ toString l ++ toString " not found in memory environment"))
                with
                | error err =>
                    erw [h_fold] at h_typecheck
                    cases h_typecheck
                | ok v =>
                    erw [h_fold] at h_typecheck
                    by_cases h_poison : poisonRef = true
                    · simp [h_poison] at h_typecheck
                      cases h_typecheck
                      rfl
                    · simp [h_poison] at h_typecheck
                      cases hpred : v.2.getD Predicate.noPred with
                      | noPred =>
                          simp [hpred, pure, Except.pure] at h_typecheck
                          cases h_typecheck
                          rfl
                      | guardOnly k =>
                          simp [hpred] at h_typecheck
                          cases htag : result1.tagEnv'[k]? with
                          | none => simp [htag, pure, Except.pure] at h_typecheck; cases h_typecheck; rfl
                          | some tv => cases tv with | mk b _ => cases b <;> simp [htag, pure, Except.pure] at h_typecheck <;> cases h_typecheck <;> rfl
                      | guardClosure k _ _ _ =>
                          simp [hpred] at h_typecheck
                          cases htag : result1.tagEnv'[k]? with
                          | none => simp [htag, pure, Except.pure] at h_typecheck; cases h_typecheck; rfl
                          | some tv => cases tv with | mk b _ => cases b <;> simp [htag, pure, Except.pure] at h_typecheck <;> cases h_typecheck <;> rfl

-- If result is clean, condition must be clean (for standard mode ite)
-- From h_poison: res.qualType.poison = joinPoison ctx.pc (joinPoison res1.poison (joinPoison res2.poison res3.poison))
-- If res is clean, then the join is false, so all components are false
lemma ite_clean_implies_cond_clean {ctx_pc res1_poison res2_poison res3_poison : Poison} :
  joinPoison ctx_pc (joinPoison res1_poison (joinPoison res2_poison res3_poison)) = false →
  res1_poison = false := by
  intro h
  have ⟨h1, h2⟩ := joinPoison_eq_false h
  have ⟨h3, _h4⟩ := joinPoison_eq_false h2
  exact h3

-- Extract guard tag directly from a predicate (helper for deref foldM lemmas).
def predGuardTag (p : Predicate) : Option Tag :=
  match p with
  | Predicate.guardClosure k _ _ _ => some k
  | Predicate.guardOnly k => some k
  | Predicate.noPred => none

-- fold function used by typecheckDeref (exposed for local reasoning)
-- Uses MemoryTypeEnv.lookup which returns Option QTyp (etyp = int for memory).
def derefFoldF (mem : MemoryTypeEnv) (acc : Bool × Option Predicate) (l : Loc) :
    Except String (Bool × Option Predicate) :=
  match mem.lookup l with
  | some qt =>
      Except.ok
        (joinPoison acc.1 qt.poison,
          match acc.2 with
          | none => some qt.pred
          | some p => some (joinPredicates p qt.pred))
  | none =>
      throw
        (toString "Location " ++ toString l ++ toString " not found in memory environment")

lemma predGuardTag_joinPredicates {p q : Predicate} {k : Tag} :
    predGuardTag (joinPredicates p q) = some k →
    predGuardTag p = some k ∧ predGuardTag q = some k := by
  cases p with
  | guardClosure k1 a1 b1 env1 =>
      cases q with
      | guardClosure k2 a2 b2 env2 =>
          intro h
          by_cases hbeq :
              beqPredicate (Predicate.guardClosure k1 a1 b1 env1)
                (Predicate.guardClosure k2 a2 b2 env2) = true
          · have hpq :
              Predicate.guardClosure k1 a1 b1 env1 = Predicate.guardClosure k2 a2 b2 env2 := by
              exact eq_of_beq (a := Predicate.guardClosure k1 a1 b1 env1)
                (b := Predicate.guardClosure k2 a2 b2 env2) hbeq
            cases hpq
            have hk1 : k1 = k := by
              simpa [joinPredicates, predGuardTag, hbeq] using h
            exact ⟨by simp [predGuardTag, hk1], by simp [predGuardTag, hk1]⟩
          · by_cases htag : (k1 == k2) = true
            · have hk1 : k1 = k := by
                simpa [joinPredicates, predGuardTag, hbeq, htag] using h
              have hk12 : k1 = k2 := of_decide_eq_true htag
              have hk2 : k2 = k := by
                calc
                  k2 = k1 := hk12.symm
                  _ = k := hk1
              exact ⟨by simp [predGuardTag, hk1], by simp [predGuardTag, hk2]⟩
            · simp [joinPredicates, predGuardTag, hbeq, htag] at h
      | guardOnly k2 =>
          intro h
          by_cases htag : (k1 == k2) = true
          · have hk1 : k1 = k := by
              simpa [joinPredicates, predGuardTag, beqPredicate, htag] using h
            have hk12 : k1 = k2 := of_decide_eq_true htag
            have hk2 : k2 = k := by
              calc
                k2 = k1 := hk12.symm
                _ = k := hk1
            exact ⟨by simp [predGuardTag, hk1], by simp [predGuardTag, hk2]⟩
          · simp [joinPredicates, predGuardTag, beqPredicate, htag] at h
      | noPred =>
          intro h
          simp [joinPredicates, predGuardTag, beqPredicate] at h
  | guardOnly k1 =>
      cases q with
      | guardClosure k2 a2 b2 env2 =>
          intro h
          by_cases htag : (k1 == k2) = true
          · have hk1 : k1 = k := by
              simpa [joinPredicates, predGuardTag, beqPredicate, htag] using h
            have hk12 : k1 = k2 := of_decide_eq_true htag
            have hk2 : k2 = k := by
              calc
                k2 = k1 := hk12.symm
                _ = k := hk1
            exact ⟨by simp [predGuardTag, hk1], by simp [predGuardTag, hk2]⟩
          · simp [joinPredicates, predGuardTag, beqPredicate, htag] at h
      | guardOnly k2 =>
          intro h
          by_cases htag : (k1 == k2) = true
          · have hk1 : k1 = k := by
              simpa [joinPredicates, predGuardTag, beqPredicate, htag] using h
            have hk12 : k1 = k2 := of_decide_eq_true htag
            have hk2 : k2 = k := by
              calc
                k2 = k1 := hk12.symm
                _ = k := hk1
            exact ⟨by simp [predGuardTag, hk1], by simp [predGuardTag, hk2]⟩
          · simp [joinPredicates, predGuardTag, beqPredicate, htag] at h
      | noPred =>
          intro h
          simp [joinPredicates, predGuardTag, beqPredicate] at h
  | noPred =>
      cases q with
      | guardClosure _ _ _ _ =>
          intro h
          simp [joinPredicates, predGuardTag, beqPredicate] at h
      | guardOnly _ =>
          intro h
          simp [joinPredicates, predGuardTag, beqPredicate] at h
      | noPred =>
          intro h
          simp [joinPredicates, predGuardTag, beqPredicate] at h

lemma list_foldlM_derefFoldF_pred_eq_guardClosure_from_some
  (mem : MemoryTypeEnv) :
  ∀ (xs : List Loc) (accPoison : Bool) (p0 : Predicate) (joined : Bool) (pred? : Option Predicate)
    (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
    List.foldlM (derefFoldF mem) (accPoison, some p0) xs = Except.ok (joined, pred?) →
    pred?.getD Predicate.noPred = Predicate.guardClosure k arg_name pred_body var_env →
    p0 = Predicate.guardClosure k arg_name pred_body var_env ∧
    (∀ l ∈ xs, ∃ qt, mem.lookup l = some qt ∧ qt.pred = Predicate.guardClosure k arg_name pred_body var_env) := by
  intro xs
  induction xs with
  | nil =>
      intro accPoison p0 joined pred? k arg_name pred_body var_env hfold hpred
      simp [List.foldlM_nil, pure, Except.pure] at hfold
      have hpred? : pred? = some p0 := by
        simpa using hfold.2.symm
      subst hpred?
      have hp0 : p0 = Predicate.guardClosure k arg_name pred_body var_env := by
        simpa using hpred
      refine ⟨hp0, ?_⟩
      intro l hl
      cases hl
  | cons x xs ih =>
      intro accPoison p0 joined pred? k arg_name pred_body var_env hfold hpred
      simp [List.foldlM_cons, bind, Except.bind] at hfold
      cases hfx : derefFoldF mem (accPoison, some p0) x with
      | error err =>
          simp [hfx] at hfold
      | ok acc' =>
          simp [hfx] at hfold
          -- Unpack the head cell: derefFoldF uses mem.lookup which returns Option QTyp.
          cases hlookup : mem.lookup x with
          | none =>
              simp [derefFoldF, hlookup] at hfx
          | some qt =>
              simp [derefFoldF, hlookup] at hfx
              have hacc'_pred : acc'.2 = some (joinPredicates p0 qt.pred) := by
                simpa using (congrArg Prod.snd hfx).symm
              have htail_fold :
                  List.foldlM (derefFoldF mem) (acc'.1, some (joinPredicates p0 qt.pred)) xs =
                    Except.ok (joined, pred?) := by
                cases acc' with
                | mk accPoison' accPred' =>
                    have haccPred : accPred' = some (joinPredicates p0 qt.pred) := by
                      simpa using hacc'_pred
                    simpa [haccPred] using hfold
              have hih :=
                ih acc'.1 (joinPredicates p0 qt.pred) joined pred? k arg_name pred_body var_env htail_fold hpred
              have hjoin := joinPredicates_eq_guardClosure (p := p0) (q := qt.pred)
                (k := k) (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env) hih.1
              refine ⟨hjoin.1, ?_⟩
              intro l hl
              rcases (List.mem_cons.mp hl) with rfl | hltail
              · refine ⟨qt, hlookup, ?_⟩
                exact hjoin.2
              · exact hih.2 l hltail

lemma list_foldlM_derefFoldF_pred_eq_guardClosure
  (mem : MemoryTypeEnv) :
  ∀ (xs : List Loc) (joined : Bool) (pred? : Option Predicate)
    (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
    List.foldlM (derefFoldF mem) (false, (none : Option Predicate)) xs = Except.ok (joined, pred?) →
    pred?.getD Predicate.noPred = Predicate.guardClosure k arg_name pred_body var_env →
    (∀ l ∈ xs, ∃ qt, mem.lookup l = some qt ∧ qt.pred = Predicate.guardClosure k arg_name pred_body var_env) := by
  intro xs
  cases xs with
  | nil =>
      intro joined pred? k arg_name pred_body var_env _hfold _hpred l hl
      cases hl
  | cons x xs =>
      intro joined pred? k arg_name pred_body var_env hfold hpred
      simp [List.foldlM_cons, bind, Except.bind] at hfold
      cases hfx : derefFoldF mem (false, none) x with
      | error err =>
          simp [hfx] at hfold
      | ok acc' =>
          simp [hfx] at hfold
          cases hlookup : mem.lookup x with
          | none =>
              simp [derefFoldF, hlookup] at hfx
          | some qt =>
              simp [derefFoldF, hlookup] at hfx
              have hacc'_pred : acc'.2 = some qt.pred := by
                  simpa using (congrArg Prod.snd hfx).symm
              have htail_fold :
                    List.foldlM (derefFoldF mem) (acc'.1, some qt.pred) xs =
                      Except.ok (joined, pred?) := by
                cases acc' with
                | mk accPoison' accPred' =>
                    have haccPred : accPred' = some qt.pred := by
                      simpa using hacc'_pred
                    simpa [haccPred] using hfold
              have hres :=
                list_foldlM_derefFoldF_pred_eq_guardClosure_from_some mem xs acc'.1 qt.pred joined pred?
                  k arg_name pred_body var_env htail_fold hpred
              have hhead_pred : qt.pred = Predicate.guardClosure k arg_name pred_body var_env :=
                hres.1
              have htail_cells := hres.2
              intro l hl
              rcases (List.mem_cons.mp hl) with rfl | hltail
              · refine ⟨qt, hlookup, hhead_pred⟩
              · exact htail_cells l hltail

lemma deref_foldM_pred_eq_guardClosure
  (mem : MemoryTypeEnv) (ls : LocSet) (joined : Bool) (pred? : Option Predicate)
  (hfold : LocSet.foldM ls (false, (none : Option Predicate)) (derefFoldF mem) =
    Except.ok (joined, pred?))
  {k : Tag} {arg_name : Name} {pred_body : PExpr} {var_env : CapturedVarEnv}
  (hpred : pred?.getD Predicate.noPred = Predicate.guardClosure k arg_name pred_body var_env)
  (l : Loc) (hl : l ∈ ls) :
  ∃ qt, mem.lookup l = some qt ∧ qt.pred = Predicate.guardClosure k arg_name pred_body var_env := by
  unfold LocSet.foldM at hfold
  rw [ExtTreeSet.foldlM_eq_foldlM_toList] at hfold
  have hl' : l ∈ ls.toList := by
    simpa using hl
  exact list_foldlM_derefFoldF_pred_eq_guardClosure mem ls.toList joined pred? k arg_name pred_body var_env hfold hpred l hl'

lemma typecheckDeref_qtypRespects
  (tm : TagMeaning) (ctx : TypeContext) (e : Expr) (fuel : Nat)
  (res res1 : TypeResult)
  (hwfTmAfter : wfTagMeaningCtx tm (ctxAfter ctx res1))
  (htc1 : typecheckExpr .ioFree ctx e fuel = .ok res1)
  (htc : typecheckDeref .ioFree ctx e (Nat.succ fuel) = .ok res) :
  QTypRespectsTagMeaning tm res.qualType := by
  have hres_etyp_int : res.qualType.etyp = ETyp.int :=
    typecheckDeref_etyp_int ctx e (Nat.succ fuel) res htc
  have hnotfun : res.qualType.etyp.isFunctionType = false := by
    simp [hres_etyp_int, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
  intro qt' k d hinq hqd
  have hself : qt' = res.qualType := QTypInQTyp_eq_of_nonFunctionTarget hinq hnotfun
  subst hself
  cases hqres : res.qualType with
  | mk etyp poison pred =>
      have hetyp_int : etyp = ETyp.int := by simpa [hqres] using hres_etyp_int
      cases hpred_res : pred with
      | noPred =>
          have : False := by
            simp [qtypGuardDesc?, hqres, hpred_res] at hqd
          exact False.elim this
      | guardOnly k0 =>
          have : False := by
            simp [qtypGuardDesc?, hqres, hpred_res] at hqd
          exact False.elim this
      | guardClosure k0 arg_name pred_body var_env =>
          have hpair : (k0, { argName := arg_name, body := pred_body, capEnv := var_env }) = (k, d) := by
            exact Option.some.inj (by simpa [qtypGuardDesc?, hqres, hpred_res] using hqd)
          cases hpair
          have hres1_etyp : ∃ ls, res1.qualType.etyp = ETyp.ref ls := by
            have htc' := htc
            simp [typecheckDeref, htc1, bind, Except.bind] at htc'
            cases hq1 : res1.qualType with
            | mk etyp1 poison1 pred1 =>
                cases etyp1 <;> simp [hq1] at htc'
                rename_i ls
                exact ⟨ls, rfl⟩
          rcases hres1_etyp with ⟨ls0, hres1_etyp0⟩
          have hls_nonempty : ls0 ≠ ∅ := by
            intro hls
            have htc_bad := htc
            cases hq1 : res1.qualType with
            | mk etyp1 poison1 pred1 =>
                have h_etyp1 : etyp1 = ETyp.ref ls0 := by
                  simpa [hq1] using hres1_etyp0
                simp [typecheckDeref, htc1, hq1, h_etyp1, hls, bind, Except.bind] at htc_bad
          have hexists_l : ∃ l, l ∈ ls0 := by
            by_contra hno
            push_neg at hno
            exact hls_nonempty ((Std.ExtTreeSet.eq_empty_iff_forall_not_mem).2 hno)
          rcases hexists_l with ⟨l0, hl0⟩
          have htc' := htc
          cases hq1 : res1.qualType with
          | mk etyp1 poison1 pred1 =>
              have h_etyp1 : etyp1 = ETyp.ref ls0 := by
                simpa [hq1] using hres1_etyp0
              simp [typecheckDeref, htc1, hq1, h_etyp1, bind, Except.bind] at htc'
              by_cases hls : ls0 = ∅
              · simp [hls] at htc'
              · simp [hls] at htc'
                cases hfold :
                    ls0.foldM (m := Except String) (false, (none : Option Predicate)) (fun x l =>
                      match res1.memEnv'.lookup l with
                      | some qt =>
                          pure (joinPoison x.1 qt.poison,
                            match x.2 with
                            | none => some qt.pred
                            | some p => some (joinPredicates p qt.pred))
                      | none =>
                          throw (toString "Location " ++ toString l ++ toString " not found in memory environment")) with
                | error err =>
                    erw [hfold] at htc'
                    cases htc'
                | ok v =>
                    erw [hfold] at htc'
                    cases hp : poison1 with
                    | true =>
                        simp [hp, pure, Except.pure] at htc'
                        have hpred_out : res.qualType.pred = Predicate.noPred := by
                          simpa using congrArg (fun r : TypeResult => r.qualType.pred) (Eq.symm htc')
                        have : False := by
                          simp [hqres, hpred_res] at hpred_out
                        exact False.elim this
                    | false =>
                        simp [hp] at htc'
                        cases hpred_fold : v.2.getD Predicate.noPred with
                        | noPred =>
                            simp [hpred_fold, pure, Except.pure] at htc'
                            have hpred_out : res.qualType.pred = Predicate.noPred := by
                              simpa using congrArg (fun r : TypeResult => r.qualType.pred) (Eq.symm htc')
                            have : False := by
                              simp [hqres, hpred_res] at hpred_out
                            exact False.elim this
                        | guardOnly k1 =>
                            cases htagopt : res1.tagEnv'.get? k1 with
                            | some tv =>
                                cases tv with
                                | mk b deps =>
                                    have htagopt' : res1.tagEnv'[k1]? = some ⟨b, deps⟩ := by
                                      simpa [Std.ExtTreeMap.get?_eq_getElem?] using htagopt
                                    cases hb : b with
                                    | true =>
                                        simp [hb, hpred_fold, htagopt', pure, Except.pure] at htc'
                                        have hpred_out : res.qualType.pred = Predicate.noPred := by
                                          simpa using congrArg (fun r : TypeResult => r.qualType.pred) (Eq.symm htc')
                                        have : False := by
                                          simp [hqres, hpred_res] at hpred_out
                                        exact False.elim this
                                    | false =>
                                        simp [hb, hpred_fold, htagopt', pure, Except.pure] at htc'
                                        have hpred_out : res.qualType.pred = Predicate.noPred := by
                                          simpa using congrArg (fun r : TypeResult => r.qualType.pred) (Eq.symm htc')
                                        have : False := by
                                          simp [hqres, hpred_res] at hpred_out
                                        exact False.elim this
                            | none =>
                                have htagopt' : res1.tagEnv'[k1]? = none := by
                                  simpa [Std.ExtTreeMap.get?_eq_getElem?] using htagopt
                                simp [hpred_fold, htagopt', pure, Except.pure] at htc'
                                have hpred_out : res.qualType.pred = Predicate.guardOnly k1 := by
                                  simpa using congrArg (fun r : TypeResult => r.qualType.pred) (Eq.symm htc')
                                have : False := by
                                  simp [hqres, hpred_res] at hpred_out
                                exact False.elim this
                        | guardClosure k1 arg1 body1 env1 =>
                            cases htagopt : res1.tagEnv'.get? k1 with
                            | some tv =>
                                cases tv with
                                | mk b deps =>
                                    have htagopt' : res1.tagEnv'[k1]? = some ⟨b, deps⟩ := by
                                      simpa [Std.ExtTreeMap.get?_eq_getElem?] using htagopt
                                    cases hb : b with
                                    | true =>
                                        simp [hb, hpred_fold, htagopt', pure, Except.pure] at htc'
                                        have hpred_out : res.qualType.pred = Predicate.noPred := by
                                          simpa using congrArg (fun r : TypeResult => r.qualType.pred) (Eq.symm htc')
                                        have : False := by
                                          simp [hqres, hpred_res] at hpred_out
                                        exact False.elim this
                                    | false =>
                                        simp [hb, hpred_fold, htagopt', pure, Except.pure] at htc'
                                        have hpred_out : res.qualType.pred = Predicate.noPred := by
                                          simpa using congrArg (fun r : TypeResult => r.qualType.pred) (Eq.symm htc')
                                        have : False := by
                                          simp [hqres, hpred_res] at hpred_out
                                        exact False.elim this
                            | none =>
                                have htagopt' : res1.tagEnv'[k1]? = none := by
                                  simpa [Std.ExtTreeMap.get?_eq_getElem?] using htagopt
                                simp [hpred_fold, htagopt', pure, Except.pure] at htc'
                                have hpred_out : res.qualType.pred = Predicate.guardClosure k1 arg1 body1 env1 := by
                                  simpa using congrArg (fun r : TypeResult => r.qualType.pred) (Eq.symm htc')
                                have hpred_eq_pred : pred = Predicate.guardClosure k1 arg1 body1 env1 := by
                                  simpa [hqres] using hpred_out
                                have hclos_eq :
                                    Predicate.guardClosure k1 arg1 body1 env1 =
                                      Predicate.guardClosure k arg_name pred_body var_env := by
                                  calc
                                    Predicate.guardClosure k1 arg1 body1 env1 = pred := by symm; exact hpred_eq_pred
                                    _ = Predicate.guardClosure k arg_name pred_body var_env := hpred_res
                                injection hclos_eq with hk1 harg1 hbody1 henv1
                                subst k1
                                subst harg1
                                subst hbody1
                                subst henv1
                                have hpred_eq :
                                    v.2.getD Predicate.noPred = Predicate.guardClosure k arg1 body1 env1 := by
                                  simp [hpred_fold]
                                obtain ⟨qtCell, hlookupCell, hpredCell⟩ :=
                                  deref_foldM_pred_eq_guardClosure res1.memEnv' ls0 v.1 v.2 hfold hpred_eq l0 hl0
                                have hlookup_ctx :
                                    (ctxAfter ctx res1).memEnv.lookup l0 = some qtCell := by
                                  simp only [ctxAfter]
                                  exact hlookupCell
                                have hqtTm :
                                    QTypRespectsTagMeaning tm qtCell :=
                                  wfTagMeaningCtx_mem_lookup_qtyp tm (ctxAfter ctx res1) l0 qtCell hwfTmAfter hlookup_ctx
                                exact hqtTm (QTypInQTyp.self qtCell) (by simp [qtypGuardDesc?, hpredCell])

-- If foldlM returns joined poison = false, then the accumulator poison is false.
lemma list_foldlM_derefFoldF_acc_false
  (mem : MemoryTypeEnv) :
  ∀ (xs : List Loc) (acc : Bool × Option Predicate) (joined : Bool) (pred? : Option Predicate),
    List.foldlM (derefFoldF mem) acc xs = Except.ok (joined, pred?) →
    joined = false →
    acc.1 = false := by
  intro xs
  induction xs with
  | nil =>
      intro acc joined pred? hfold hjoin
      simp [List.foldlM_nil, pure, Except.pure] at hfold
      cases hfold
      simpa using hjoin
  | cons x xs ih =>
      intro acc joined pred? hfold hjoin
      simp [List.foldlM_cons, bind, Except.bind] at hfold
      cases hfx : derefFoldF mem acc x with
      | error err =>
          simp [hfx] at hfold
      | ok acc' =>
          simp [hfx] at hfold
          -- unfold derefFoldF to relate acc'.1 to acc.1
          cases hlookup : mem.lookup x with
          | none =>
              simp [derefFoldF, hlookup] at hfx
          | some qt =>
              simp [derefFoldF, hlookup] at hfx
              have hacc'_fst : acc'.1 = joinPoison acc.1 qt.poison := by
                simpa using (congrArg Prod.fst hfx).symm
              have hacc'_false : acc'.1 = false := ih acc' joined pred? hfold hjoin
              have hjoin' : joinPoison acc.1 qt.poison = false := by
                simpa [hacc'_fst] using hacc'_false
              exact (joinPoison_eq_false hjoin').1

-- If foldlM returns joined poison = false, then every referenced cell is unpoisoned.
lemma list_foldlM_derefFoldF_poison_false
  (mem : MemoryTypeEnv) :
  ∀ (xs : List Loc) (acc : Bool × Option Predicate) (joined : Bool) (pred? : Option Predicate),
    List.foldlM (derefFoldF mem) acc xs = Except.ok (joined, pred?) →
    joined = false →
    ∀ l ∈ xs, ∃ qt, mem.lookup l = some qt ∧ qt.poison = false := by
  intro xs
  induction xs with
  | nil =>
      intro acc joined pred? hfold _hjoin l hl
      cases hl
  | cons x xs ih =>
      intro acc joined pred? hfold hjoin l hl
      simp [List.foldlM, bind, Except.bind] at hfold
      cases hfx : derefFoldF mem acc x with
      | error err =>
          simp [hfx] at hfold
      | ok acc' =>
          simp [hfx] at hfold
          -- extract the head cell from hfx
          cases hlookup : mem.lookup x with
          | none =>
              simp [derefFoldF, hlookup] at hfx
          | some qt =>
              simp [derefFoldF, hlookup] at hfx
              have hacc' : acc'.1 = joinPoison acc.1 qt.poison := by
                  simpa using (congrArg Prod.fst hfx).symm
              have hacc'_false : acc'.1 = false :=
                list_foldlM_derefFoldF_acc_false mem xs acc' joined pred? hfold hjoin
              have hpoison_head : qt.poison = false := by
                have hjoin' : joinPoison acc.1 qt.poison = false := by simpa [hacc'] using hacc'_false
                exact (joinPoison_eq_false hjoin').2
              rcases (List.mem_cons.mp hl) with heq | hltail
              · subst heq
                exact ⟨qt, hlookup, hpoison_head⟩
              · exact ih acc' joined pred? hfold hjoin l hltail

-- If foldlM succeeds, then every referenced cell has type int.
lemma list_foldlM_derefFoldF_etyp_int
  (mem : MemoryTypeEnv) :
  ∀ (xs : List Loc) (acc : Bool × Option Predicate) (joined : Bool) (pred? : Option Predicate),
    List.foldlM (derefFoldF mem) acc xs = Except.ok (joined, pred?) →
    ∀ l ∈ xs, ∃ qt, mem.lookup l = some qt := by
  intro xs
  induction xs with
  | nil =>
      intro acc joined pred? hfold l hl
      cases hl
  | cons x xs ih =>
      intro acc joined pred? hfold l hl
      simp [List.foldlM, bind, Except.bind] at hfold
      cases hfx : derefFoldF mem acc x with
      | error err =>
          simp [hfx] at hfold
      | ok acc' =>
          simp [hfx] at hfold
          cases hlookup : mem.lookup x with
          | none =>
              simp [derefFoldF, hlookup] at hfx
          | some qt =>
              simp [derefFoldF, hlookup] at hfx
              rcases (List.mem_cons.mp hl) with rfl | hltail
              · exact ⟨qt, hlookup⟩
              · exact ih acc' joined pred? hfold l hltail

-- If foldlM returns a guard tag k, then every referenced cell predicate has tag k.
lemma list_foldlM_derefFoldF_guardTag
  (mem : MemoryTypeEnv) :
  ∀ (xs : List Loc) (acc : Bool × Option Predicate) (joined : Bool) (pred? : Option Predicate) (k : Tag),
    List.foldlM (derefFoldF mem) acc xs = Except.ok (joined, pred?) →
    predGuardTag (pred?.getD Predicate.noPred) = some k →
    (predGuardTag (acc.2.getD Predicate.noPred) = some k ∨ acc.2 = none) ∧
    (∀ l ∈ xs, ∃ qt, mem.lookup l = some qt ∧ predGuardTag qt.pred = some k) := by
  intro xs
  induction xs with
  | nil =>
      intro acc joined pred? k hfold hguard
      simp [List.foldlM, pure, Except.pure] at hfold
      cases hfold
      constructor
      · left
        simpa using hguard
      · intro l hl; cases hl
  | cons x xs ih =>
      intro acc joined pred? k hfold hguard
      simp [List.foldlM, bind, Except.bind] at hfold
      cases hfx : derefFoldF mem acc x with
      | error err =>
          simp [hfx] at hfold
      | ok acc' =>
          simp [hfx] at hfold
          -- extract head cell info
          cases hlookup : mem.lookup x with
          | none =>
              simp [derefFoldF, hlookup] at hfx
          | some qt =>
              simp [derefFoldF, hlookup] at hfx
              have hacc'_snd :
                    acc'.2 =
                      match acc.2 with
                      | none => some qt.pred
                      | some p => some (joinPredicates p qt.pred) := by
                simpa using (congrArg Prod.snd hfx).symm
              have ih' := ih acc' joined pred? k hfold hguard
              rcases ih' with ⟨hacc'_tag, htail⟩
              have hhead_tag : predGuardTag qt.pred = some k := by
                  -- acc'.2 is some predHead by construction
                  -- Use hacc'_tag to derive head tag
                  cases hacc : acc.2 with
                  | none =>
                      have hacc'_snd' : acc'.2 = some qt.pred := by
                        simpa [hacc] using hacc'_snd
                      -- acc'.2 = some qt.pred
                      have hk : predGuardTag (acc'.2.getD Predicate.noPred) = some k := by
                        cases hacc'_tag with
                        | inl hk => exact hk
                        | inr hnone =>
                            simp [hacc'_snd'] at hnone
                      simpa [hacc'_snd'] using hk
                  | some p =>
                      have hacc'_snd' : acc'.2 = some (joinPredicates p qt.pred) := by
                        simpa [hacc] using hacc'_snd
                      have hk : predGuardTag (acc'.2.getD Predicate.noPred) = some k := by
                        cases hacc'_tag with
                        | inl hk => exact hk
                        | inr hnone =>
                           simp [hacc'_snd'] at hnone
                      -- unfold acc'.2 and use joinPredicates lemma
                      have hpred : predGuardTag (joinPredicates p qt.pred) = some k := by
                        simpa [hacc'_snd'] using hk
                      exact (predGuardTag_joinPredicates hpred).2
              constructor
              · -- propagate tag to accumulator (or none)
                  cases hacc : acc.2 with
                  | none =>
                      right; rfl
                  | some p =>
                      -- acc'.2 = joinPredicates p qt.pred, so tag on acc'.2 gives tag on p
                      have hacc'_snd' : acc'.2 = some (joinPredicates p qt.pred) := by
                        simpa [hacc] using hacc'_snd
                      have hk : predGuardTag (acc'.2.getD Predicate.noPred) = some k := by
                        cases hacc'_tag with
                        | inl hk => exact hk
                        | inr hnone =>
                            simp [hacc'_snd'] at hnone
                      have hpred : predGuardTag (joinPredicates p qt.pred) = some k := by
                        simpa [hacc'_snd'] using hk
                      left
                      exact (predGuardTag_joinPredicates hpred).1
              · intro l hl
                rcases (List.mem_cons.mp hl) with rfl | hltail
                · exact ⟨qt, hlookup, hhead_tag⟩
                · exact htail l hltail

lemma deref_foldM_poison_false
  (mem : MemoryTypeEnv) (ls : LocSet) (joined : Bool) (pred? : Option Predicate)
  (hfold : LocSet.foldM ls (false, (none : Option Predicate)) (derefFoldF mem) =
    Except.ok (joined, pred?))
  (hjoin : joined = false) (l : Loc) (hl : l ∈ ls) :
  ∃ qt, mem.lookup l = some qt ∧ qt.poison = false := by
  -- Convert to list fold and apply list lemma
  unfold LocSet.foldM at hfold
  rw [ExtTreeSet.foldlM_eq_foldlM_toList] at hfold
  have hl' : l ∈ ls.toList := by
    -- lemma in Std.ExtTreeSet.Lemmas
    simpa using hl
  exact list_foldlM_derefFoldF_poison_false mem ls.toList (false, none) joined pred? hfold hjoin l hl'

lemma deref_foldM_guardTag
  (mem : MemoryTypeEnv) (ls : LocSet) (joined : Bool) (pred? : Option Predicate) (k : Tag)
  (hfold : LocSet.foldM ls (false, (none : Option Predicate)) (derefFoldF mem) =
    Except.ok (joined, pred?))
  (hguard : predGuardTag (pred?.getD Predicate.noPred) = some k)
  (l : Loc) (hl : l ∈ ls) :
  ∃ qt, mem.lookup l = some qt ∧ predGuardTag qt.pred = some k := by
  unfold LocSet.foldM at hfold
  rw [ExtTreeSet.foldlM_eq_foldlM_toList] at hfold
  have hl' : l ∈ ls.toList := by
    simpa using hl
  have haux :=
    list_foldlM_derefFoldF_guardTag mem ls.toList (false, none) joined pred? k hfold hguard
  exact (haux.2 l hl')

lemma deref_foldM_etyp_int
  (mem : MemoryTypeEnv) (ls : LocSet) (joined : Bool) (pred? : Option Predicate)
  (hfold : LocSet.foldM ls (false, (none : Option Predicate)) (derefFoldF mem) =
    Except.ok (joined, pred?))
  (l : Loc) (hl : l ∈ ls) :
  ∃ qt, mem.lookup l = some qt := by
  unfold LocSet.foldM at hfold
  rw [ExtTreeSet.foldlM_eq_foldlM_toList] at hfold
  have hl' : l ∈ ls.toList := by
    simpa using hl
  exact list_foldlM_derefFoldF_etyp_int mem ls.toList (false, none) joined pred? hfold l hl'

-- wfTypeContext for ctxAfter is equivalent to wfTypeResult
-- (ctxAfter sets memEnv := res.memEnv' and nextLoc := res.nextLoc')
lemma wfTypeResult_of_wfTypeContext_ctxAfter (ctx : TypeContext) (res : TypeResult) :
  wfTypeContext (ctxAfter ctx res) → wfTypeResult res := by
  simp only [wfTypeContext, ctxAfter, wfTypeResult]
  exact id

-- If l is not in ctx.memEnv and runtimeInstantiatesCtx holds, then θ.lookup l = none
-- (contrapositive of runtimeInstantiatesCtx's first conjunct)
lemma theta_not_contains_if_not_in_memEnv
  (ctx : TypeContext) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) (l : Loc) :
  runtimeInstantiatesCtx ctx μ ρ θ →
  ¬ ctx.memEnv.contains l →
  θ.lookup l = none := by
  intro hric hnotContains
  by_contra h
  push_neg at h
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 h
  have ⟨hcontains, _⟩ := hric.1 l a ha
  exact hnotContains hcontains

lemma wfExtendsMap_trans {θ₀ θ₁ θ₂ : RealizationMap} :
  wfExtendsMap θ₀ θ₁ → wfExtendsMap θ₁ θ₂ → wfExtendsMap θ₀ θ₂ := by
  intro h01 h12
  refine ⟨?_, ?_⟩
  · intro l a hlookup
    have h1 : θ₁.lookup l = some a := h01.1 l a hlookup
    exact h12.1 l a h1
  · intro hWF0
    have hWF1 : wfRealizationMap θ₁ := h01.2 hWF0
    exact h12.2 hWF1

lemma wfValue_mono_of_le_nextAddr {n m : Address} (h : n ≤ m) (x : Name) (v : Value) :
  wfValue n v → wfValue m v := by
  intro hv
  let cfg : Config :=
    { memory := (∅ : Memory), varEnv := [(x, v)], nextAddr := n, pureMode := false }
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

-- Bridge lemma: top-level agreement premises imply the step-level invariant.
-- This is the key link from spec-driven premises to the context-driven StepFR.
lemma agreeOnCriticalAndTrusted_implies_agreeOnClean
  (predSat : PredSat) (R : Regime) (s : InputSpec) (ctx : TypeContext)
  (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ θ₁ : RealizationMap) :
  ctxMatchesInputSpec s ctx →
  agreeOnCriticalInputsUnderRegimeSpec predSat R s μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ →
  agreeOnTrustedInputs predSat R s ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ →
  agreeOnClean predSat R ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ := by
  intro hctx hcrit htrusted
  rcases hctx with ⟨hctx_mem, hctx_vars, _, _⟩
  rcases hcrit with ⟨hcrit_locs, hcrit_vars⟩
  rcases htrusted with ⟨htrusted_locs, htrusted_vars⟩
  constructor
  · intro l qt hctx_lookup hclean
    by_cases hkey : s.locs.hasKey l
    · -- Critical location: use agreement from the input spec.
      have hcontains : s.locs.contains l = true := by
        simpa [MemoryTypeEnv.hasKey] using hkey
      have hmem : l ∈ s.locs :=
        (Std.ExtTreeMap.contains_iff_mem).1 hcontains
      have hlookup_isSome : (s.locs[l]?).isSome = true :=
        (Std.ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
      cases hlookup_s : s.locs[l]? with
      | none =>
          simp [hlookup_s] at hlookup_isSome
      | some e_s =>
          let qt_s : QTyp := ⟨ETyp.int, e_s.poison, e_s.pred⟩
          have hlookup_s' : s.locs.lookup l = some qt_s := by
            simp only [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?, hlookup_s, Option.map]; rfl
          have hctx_lookup' : ctx.memEnv.lookup l = some qt_s := hctx_mem hlookup_s'
          have hqt : qt_s = qt := by
            have : some qt_s = some qt := by
              calc
                some qt_s = ctx.memEnv.lookup l := by
                  symm
                  exact hctx_lookup'
                _ = some qt := by
                  exact hctx_lookup
            exact Option.some.inj this
          have hcrit_locs' := hcrit_locs
          rw [List.forall_iff_forall_mem] at hcrit_locs'
          have hmem' : (l, qt_s) ∈ memEnvToLocQTypList s.locs := by
            rw [memEnvToLocQTypList, List.mem_map]
            refine ⟨(l, e_s), (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some).2 hlookup_s, ?_⟩
            rfl
          have hlocEntry : agreeLocUnder predSat R μ₀ μ₁ θ₀ θ₁ (l, qt_s) :=
            hcrit_locs' (l, qt_s) hmem'
          simpa [hqt] using hlocEntry
    · -- Trusted location: use trusted-input agreement.
      exact htrusted_locs l qt hctx_lookup hkey hclean
  · intro x qt hctx_lookup hclean
    by_cases hkey : s.vars.hasKey x
    · -- Critical variable: use agreement from the input spec.
      have hcontains : s.vars.contains x = true := by
        simpa [VarTypeEnv.hasKey] using hkey
      have hmem : x ∈ s.vars :=
        (Std.ExtTreeMap.contains_iff_mem).1 hcontains
      have hlookup_isSome : (s.vars[x]?).isSome = true :=
        (Std.ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
      cases hlookup_s : s.vars[x]? with
      | none =>
          simp [hlookup_s] at hlookup_isSome
      | some qt_s =>
          have hlookup_s : s.vars.lookup x = some qt_s := by
            simpa [VarTypeEnv.lookup] using hlookup_s
          have hctx_lookup' : ctx.varEnv.lookup x = some qt_s := hctx_vars hlookup_s
          have hqt : qt_s = qt := by
            have : some qt_s = some qt := by
              calc
                some qt_s = ctx.varEnv.lookup x := by
                  symm
                  exact hctx_lookup'
                _ = some qt := by
                  exact hctx_lookup
            exact Option.some.inj this
          have hcrit_vars' := hcrit_vars
          rw [List.forall_iff_forall_mem] at hcrit_vars'
          have hmem' : (x, qt_s) ∈ s.vars.toList := by
            rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some]
            dsimp [VarTypeEnv.lookup] at hlookup_s
            simpa using hlookup_s
          have hvarEntry : agreeVarUnder predSat R μ₀ ρ₀ μ₁ ρ₁ θ₀ θ₁ (x, qt_s) :=
            hcrit_vars' (x, qt_s) hmem'
          simpa [hqt] using hvarEntry
    · -- Trusted variable: use trusted-input agreement.
      exact htrusted_vars x qt hctx_lookup hkey hclean

-- Bridge theorem: connects the step theorem to the top-level FR spec.
theorem TypeSystemEnforcesFaultRobustness_impl :
  (∀ (mode : LeanPoison.EvalMode) e ctxᵢ predSat tm,
    TypeSystemEnforcesFaultRobustness_step_spec mode e ctxᵢ predSat tm) →
  (∀ e s obs, TypeSystemEnforcesFaultRobustness_spec e s obs) := by
  intro hstep e s obs
  rintro his _hos ctx hctx _hwf _hpc _hte predSat tm _hwfTm _hps ⟨fuel, res, htc, hobs⟩
  rcases hobs with ⟨hobs_ret, hobs_mem⟩
  intro mode μ₁ μ₂ ρ₁ ρ₂ θ₁ θ₂ a₁ a₂ pm
  have hstep' := hstep mode e ctx predSat tm
  have hstep' := hstep' fuel res htc
  intro cf₁ cf₂ o₁ o₂ hR hRbound hregBounded hθ₁ hθ₂ hwfcfg₁ hwfcfg₂ hics₁ hics₂ hric₁ hric₂ htrustedInit₁ htrustedInit₂ hcrs₁ hcrs₂ hagree htrusted ht₁ ht₂
  set R := ctx.regime with hRdef
  -- Use bridge lemma to derive consistentWithRegime from consistentRegimeSpec
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
  have hagree_clean :
      agreeOnClean predSat R ctx μ₁ ρ₁ θ₁ μ₂ ρ₂ θ₂ :=
    agreeOnCriticalAndTrusted_implies_agreeOnClean
      predSat R s ctx μ₁ μ₂ ρ₁ ρ₂ θ₁ θ₂ hctx hagree htrusted
  have htagR : tagEnvConsistentWithRegime ctx.tagEnv R := by
    intro k deps hlookup
    -- Empty tag environment at the top level.
    have : (ctx.tagEnv.get? k) = none := by
      simp [_hte]
    rw [this] at hlookup
    cases hlookup
  have hreg : regimeConsistentWithCtx ctx := by
    refine ⟨htagR, ?_⟩
    -- At the top level, `R.bound = ctx.nextTag`.
    exact Nat.le_of_eq hR
  have hstepFR :=
    hstep' _hps _hwfTm μ₁ μ₂ ρ₁ ρ₂ θ₁ θ₂ cf₁ cf₂ o₁ o₂
      hθ₁ hθ₂ _hwf hric₁ hric₂ hreg hregBounded hcwr₁ hcwr₂ hagree_clean
      a₁ a₂ pm hwfcfg₁ hwfcfg₂ ht₁ ht₂
  rcases hstepFR with ⟨_hresTm, hstepFR⟩
  rcases hstepFR with ⟨θ₁', θ₂', hθ₁ext, hθ₂ext, _hvtyp₁, _hvtyp₂, _hTm', _hwf', _hwfcf₁', _hwfcf₂', _hric₁', _hric₂', _hreg', _hcwr₁', _hcwr₂', hagree_clean', _hval_consist₁, _hval_consist₂, hret_agree⟩
  refine ⟨θ₁', θ₂', hθ₁ext, hθ₂ext, ?_⟩
  -- Bridge from post-state agreement to observables.
  simp [observablesEqual]
  constructor
  · intro l et hobs_lookup
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
  · cases hretOpt : obs.retEtyp? with
    | none =>
        simp
    | some et =>
        -- Use return agreement from the step proof.
        rcases hobs_ret _ hretOpt with ⟨hret_et, hret_poison⟩
        have hret_notfun_obs : et.isFunctionType = false := by
          simpa [wfObsSpec, hretOpt] using _hos
        -- Use output regime since hret_agree now uses (ctxAfter ctx res).regime
        have hret_clean : qtypCleanUnder (ctxAfter ctx res).regime res.qualType := by
          exact qtypCleanUnder.clean hret_poison
        have hret_agree' :
            agreeValueUnder predSat (ctxAfter ctx res).regime cf₁.memory cf₂.memory θ₁' θ₂' res.qualType o₁ o₂ :=
          hret_agree hret_clean
        cases et with
        | ref ls =>
            cases hret_agree' with
            | @clean_ref ls' l a₁ a₂ _qt v₁ v₂ hpoison hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                have hls_eq : ls' = ls := by injection (hret_et.symm.trans hetyp); exact ‹ls = ls'›.symm
                exact And.intro
                  ⟨l, And.intro (hls_eq ▸ hin) (Exists.intro a₁ (And.intro hlookup1 hv1))⟩
                  ⟨l, And.intro (hls_eq ▸ hin) (Exists.intro a₂ (And.intro hlookup2 hv2))⟩
            | @withPred_true_ref k ls' l a₁ a₂ _qt v₁ v₂ htag hregime hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                have hls_eq : ls' = ls := by injection (hret_et.symm.trans hetyp); exact ‹ls = ls'›.symm
                exact And.intro
                  ⟨l, And.intro (hls_eq ▸ hin) (Exists.intro a₁ (And.intro hlookup1 hv1))⟩
                  ⟨l, And.intro (hls_eq ▸ hin) (Exists.intro a₂ (And.intro hlookup2 hv2))⟩
            | clean_eq_nonref_nonarrow _ _ hnotref _ =>
                have : False := by
                  apply hnotref
                  exact ⟨ls, hret_et⟩
                exact False.elim this
            | withPred_true_eq _ _ _ _ hnotref _ =>
                have : False := by
                  apply hnotref
                  exact ⟨ls, hret_et⟩
                exact False.elim this
            | clean_internal_arrow _ hetyp _ _ _ _ _ _ _ =>
                cases (Eq.trans (Eq.symm hetyp) hret_et)
            | dirty_internal_arrow _ hisArrow =>
                -- qt.etyp is an arrow but hret_et says it's et (from observable spec).
                -- This would contradict if observable types are not function types.
                have : (ETyp.ref ls).isArrow = true := by
                  simpa [hret_et] using hisArrow
                -- But references are not arrow types.
                have : (false : Bool) = true := by
                  simp [ETyp.isArrow] at this
                cases this
            | clean_internal_parrow _ hetyp _ _ _ _ _ _ _ =>
                cases (Eq.trans (Eq.symm hetyp) hret_et)
            | dirty_internal_parrow _ hisParrow =>
                -- qt.etyp is a parrow but hret_et says it's et (from observable spec).
                -- This would contradict if observable types are not function types.
                have : (ETyp.ref ls).isParrow = true := by
                  simpa [hret_et] using hisParrow
                -- But references are not parrow types.
                have : (false : Bool) = true := by
                  simp [ETyp.isParrow] at this
                cases this
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

end TypeSystemEnforcesFaultRobustness_impl_proof

section TypeSystemEnforcesFaultRobustness_step_proof

lemma agreeValueUnder_of_agreeVarUnder
  {predSat : PredSat} {R : Regime} {μ₀ μ₁ : Memory} {ρ₀ ρ₁ : VarEnv}
  {θ₀ θ₁ : RealizationMap} {x : Name} {qt : QTyp} {v₀ v₁ : Value} :
  agreeVarUnder predSat R μ₀ ρ₀ μ₁ ρ₁ θ₀ θ₁ (x, qt) →
  ρ₀.lookup x = some v₀ →
  ρ₁.lookup x = some v₁ →
  agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ := by
  intro hvar hlookup₀ hlookup₁
  cases hvar with
  | agree_values _ _ v₀' v₁' hlookup₀' hlookup₁' hagree =>
      have hv₀ : v₀' = v₀ := by
        have : some v₀' = some v₀ := by
          calc
            some v₀' = ρ₀.lookup x := by symm; exact hlookup₀'
            _ = some v₀ := by exact hlookup₀
        exact Option.some.inj this
      have hv₁ : v₁' = v₁ := by
        have : some v₁' = some v₁ := by
          calc
            some v₁' = ρ₁.lookup x := by symm; exact hlookup₁'
            _ = some v₁ := by exact hlookup₁
        exact Option.some.inj this
      simpa [hv₀, hv₁] using hagree
  | both_none _ _ hnone₀ _ =>
      have : False := by
        have : some v₀ = none := by
          calc
            some v₀ = ρ₀.lookup x := by symm; exact hlookup₀
            _ = none := by exact hnone₀
        cases this
      exact False.elim this

lemma valueHasETyp_extends
  {θ₀ θ₁ : RealizationMap} {v : Value} {t : ETyp} :
  θ₀.extendsMap θ₁ →
  valueHasETyp θ₀ v t →
  valueHasETyp θ₁ v t := by
  intro hExt hval
  induction hval generalizing θ₁ with
  | num n =>
      exact valueHasETyp.num n
  | bool b =>
      exact valueHasETyp.bool b
  | unit =>
      exact valueHasETyp.unit
  | str s =>
      exact valueHasETyp.str s
  | loc hlookup hin =>
      exact valueHasETyp.loc (hExt _ _ hlookup) hin
  | closure htcl henv hcover ih =>
      refine valueHasETyp.closure (htcl := htcl) (hcover := hcover) ?_
      intro y qt v hlookupT hlookupV
      exact ih y qt v hlookupT hlookupV hExt
  | peClosure hpure htcl henv hcover ih =>
      refine valueHasETyp.peClosure (hpure := hpure) (htcl := htcl) (hcover := hcover) ?_
      intro y qt v hlookupT hlookupV
      exact ih y qt v hlookupT hlookupV hExt

lemma agreeValueUnder_clean_extends
  {predSat : PredSat} {R : Regime} {μ₀ μ₁ μ₀' μ₁' : Memory}
  {θ₀ θ₁ θ₀' θ₁' : RealizationMap} {qt : QTyp} {v₀ v₁ : Value} :
  (∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ₀ v ↔ qtypPredHolds predSat qt μ₀' v) →
  (∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ₁ v ↔ qtypPredHolds predSat qt μ₁' v) →
  qtypCleanUnder R qt →
  θ₀.extendsMap θ₀' →
  θ₁.extendsMap θ₁' →
  agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ →
  agreeValueUnder predSat R μ₀' μ₁' θ₀' θ₁' qt v₀ v₁ := by
  intro hpred_compat₀ hpred_compat₁ hclean hθ₀ hθ₁ hagree
  let motive₁ :
      (a : QTyp) → (a_1 a_2 : Value) → agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ a a_1 a_2 → Prop :=
    fun qt v₁ v₂ _ =>
      qtypCleanUnder R qt →
        (∀ (qt : QTyp) (v : Value),
          qtypPredHolds predSat qt μ₀ v ↔ qtypPredHolds predSat qt μ₀' v) →
          (∀ (qt : QTyp) (v : Value),
            qtypPredHolds predSat qt μ₁ v ↔ qtypPredHolds predSat qt μ₁' v) →
            θ₀.extendsMap θ₀' →
              θ₁.extendsMap θ₁' →
                agreeValueUnder predSat R μ₀' μ₁' θ₀' θ₁' qt v₁ v₂
  let motive₂ :
      (a : CapturedVarEnv) → (a_1 a_2 : VarEnv) → agreeCapturedEnv predSat R μ₀ μ₁ θ₀ θ₁ a a_1 a_2 → Prop :=
    fun σcap ρcap₁ ρcap₂ _ =>
      (∀ (qt : QTyp) (v : Value),
        qtypPredHolds predSat qt μ₀ v ↔ qtypPredHolds predSat qt μ₀' v) →
        (∀ (qt : QTyp) (v : Value),
          qtypPredHolds predSat qt μ₁ v ↔ qtypPredHolds predSat qt μ₁' v) →
          θ₀.extendsMap θ₀' →
            θ₁.extendsMap θ₁' →
              agreeCapturedEnv predSat R μ₀' μ₁' θ₀' θ₁' σcap ρcap₁ ρcap₂
  have htransport : motive₁ qt v₀ v₁ hagree :=
    agreeValueUnder.rec (predSat := predSat) (R := R) (μ₁ := μ₀) (μ₂ := μ₁) (θ₁ := θ₀) (θ₂ := θ₁)
      (motive_1 := motive₁) (motive_2 := motive₂)
      (clean_eq_nonref_nonarrow := by
        intro qt v₁ v₂ hpoison hnotfun hnotref hagree _hclean _hpred_compat₀ _hpred_compat₁ _hθ₀ _hθ₁
        exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison hnotfun hnotref hagree)
      (clean_internal_arrow := by
        intro st1 st2 p tcls qt tcl x body σcap ρcap₁ ρcap₂ v₁ v₂ hclean_internal hetyp htcl hmatch hcap
          hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ hv₁ hv₂ ihCap _hclean hpred_compat₀ hpred_compat₁ hθ₀ hθ₁
        exact agreeValueUnder.clean_internal_arrow hclean_internal hetyp htcl hmatch
          (ihCap hpred_compat₀ hpred_compat₁ hθ₀ hθ₁)
          (memberVarsRegimeEvidence_transport_μ hpred_compat₀ hmemberVars₁)
          (memberCvcrEvidence_transport_μ_θ hpred_compat₀ hθ₀ hmemberCvcr₁)
          (memberVarsRegimeEvidence_transport_μ hpred_compat₁ hmemberVars₂)
          (memberCvcrEvidence_transport_μ_θ hpred_compat₁ hθ₁ hmemberCvcr₂)
          hv₁ hv₂)
      (dirty_internal_arrow := by
        intro qt v₁ v₂ hdirty hisArrow htyp1 htyp2 _hclean _hpred_compat₀ _hpred_compat₁ hθ₀ hθ₁
        exact agreeValueUnder.dirty_internal_arrow hdirty hisArrow
          (valueHasETyp_extends hθ₀ htyp1) (valueHasETyp_extends hθ₁ htyp2))
      (clean_internal_parrow := by
        intro st1 st2 p tcls qt tcl x body pbody σcap ρcap₁ ρcap₂ v₁ v₂ hclean_internal hetyp htcl hmatch hcap
          hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ hv₁ hv₂ ihCap _hclean hpred_compat₀ hpred_compat₁ hθ₀ hθ₁
        exact agreeValueUnder.clean_internal_parrow hclean_internal hetyp htcl hmatch
          (ihCap hpred_compat₀ hpred_compat₁ hθ₀ hθ₁)
          (memberVarsRegimeEvidence_transport_μ hpred_compat₀ hmemberVars₁)
          (memberCvcrEvidence_transport_μ_θ hpred_compat₀ hθ₀ hmemberCvcr₁)
          (memberVarsRegimeEvidence_transport_μ hpred_compat₁ hmemberVars₂)
          (memberCvcrEvidence_transport_μ_θ hpred_compat₁ hθ₁ hmemberCvcr₂)
          hv₁ hv₂)
      (dirty_internal_parrow := by
        intro qt v₁ v₂ hdirty hisParrow htyp1 htyp2 _hclean _hpred_compat₀ _hpred_compat₁ hθ₀ hθ₁
        exact agreeValueUnder.dirty_internal_parrow hdirty hisParrow
          (valueHasETyp_extends hθ₀ htyp1) (valueHasETyp_extends hθ₁ htyp2))
      (clean_ref := by
        intro ls l a₁ a₂ qt v₁ v₂ hpoison hetyp hlookup1 hin hv1 hlookup2 hv2 _hclean _hpred_compat₀ _hpred_compat₁ hθ₀ hθ₁
        exact agreeValueUnder.clean_ref hpoison hetyp (hθ₀ _ _ hlookup1) hin hv1 (hθ₁ _ _ hlookup2) hv2)
      (withPred_true_eq := by
        intro k qt v₁ v₂ htag hregime hnotfun hnotref hagree _hclean _hpred_compat₀ _hpred_compat₁ _hθ₀ _hθ₁
        exact agreeValueUnder.withPred_true_eq k htag hregime hnotfun hnotref hagree)
      (withPred_true_ref := by
        intro k ls l a₁ a₂ qt v₁ v₂ htag hregime hetyp hlookup1 hin hv1 hlookup2 hv2 _hclean _hpred_compat₀ _hpred_compat₁ hθ₀ hθ₁
        exact agreeValueUnder.withPred_true_ref k htag hregime hetyp
          (hθ₀ _ _ hlookup1) hin hv1 (hθ₁ _ _ hlookup2) hv2)
      (nil := by
        intro ρcap₁ ρcap₂ _hpred_compat₀ _hpred_compat₁ _hθ₀ _hθ₁
        exact agreeCapturedEnv.nil)
      (cons_clean := by
        intro x qt σcap ρcap₁ ρcap₂ v₁ v₂ hclean hlookup1 hlookup2 htyp1 htyp2 hagree htail ihAgree ihTail
          hpred_compat₀ hpred_compat₁ hθ₀ hθ₁
        exact agreeCapturedEnv.cons_clean hclean hlookup1 hlookup2
          (valueHasETyp_extends hθ₀ htyp1) (valueHasETyp_extends hθ₁ htyp2)
          (ihAgree hclean hpred_compat₀ hpred_compat₁ hθ₀ hθ₁)
          (ihTail hpred_compat₀ hpred_compat₁ hθ₀ hθ₁))
      (cons_dirty := by
        intro x qt σcap ρcap₁ ρcap₂ v₁ v₂ hdirty hlookup1 hlookup2 htyp1 htyp2 htail ihTail
          hpred_compat₀ hpred_compat₁ hθ₀ hθ₁
        exact agreeCapturedEnv.cons_dirty hdirty hlookup1 hlookup2
          (valueHasETyp_extends hθ₀ htyp1) (valueHasETyp_extends hθ₁ htyp2)
          (ihTail hpred_compat₀ hpred_compat₁ hθ₀ hθ₁))
      hagree
  exact htransport hclean hpred_compat₀ hpred_compat₁ hθ₀ hθ₁

lemma agreeCapturedEnv_clean_extends
  {predSat : PredSat} {R : Regime} {μ₀ μ₁ μ₀' μ₁' : Memory}
  {θ₀ θ₁ θ₀' θ₁' : RealizationMap} {σcap : CapturedVarEnv} {ρcap₀ ρcap₁ : VarEnv} :
  (∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ₀ v ↔ qtypPredHolds predSat qt μ₀' v) →
  (∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ₁ v ↔ qtypPredHolds predSat qt μ₁' v) →
  θ₀.extendsMap θ₀' →
  θ₁.extendsMap θ₁' →
  agreeCapturedEnv predSat R μ₀ μ₁ θ₀ θ₁ σcap ρcap₀ ρcap₁ →
  agreeCapturedEnv predSat R μ₀' μ₁' θ₀' θ₁' σcap ρcap₀ ρcap₁ := by
  intro hpred_compat₀ hpred_compat₁ hθ₀ hθ₁ hcap
  let motive₁ :
      (a : QTyp) → (a_1 a_2 : Value) → agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ a a_1 a_2 → Prop :=
    fun qt v₁ v₂ _ =>
      qtypCleanUnder R qt →
        (∀ (qt : QTyp) (v : Value),
          qtypPredHolds predSat qt μ₀ v ↔ qtypPredHolds predSat qt μ₀' v) →
          (∀ (qt : QTyp) (v : Value),
            qtypPredHolds predSat qt μ₁ v ↔ qtypPredHolds predSat qt μ₁' v) →
            θ₀.extendsMap θ₀' →
              θ₁.extendsMap θ₁' →
                agreeValueUnder predSat R μ₀' μ₁' θ₀' θ₁' qt v₁ v₂
  let motive₂ :
      (a : CapturedVarEnv) → (a_1 a_2 : VarEnv) → agreeCapturedEnv predSat R μ₀ μ₁ θ₀ θ₁ a a_1 a_2 → Prop :=
    fun σcap ρcap₁ ρcap₂ _ =>
      (∀ (qt : QTyp) (v : Value),
        qtypPredHolds predSat qt μ₀ v ↔ qtypPredHolds predSat qt μ₀' v) →
        (∀ (qt : QTyp) (v : Value),
          qtypPredHolds predSat qt μ₁ v ↔ qtypPredHolds predSat qt μ₁' v) →
          θ₀.extendsMap θ₀' →
            θ₁.extendsMap θ₁' →
              agreeCapturedEnv predSat R μ₀' μ₁' θ₀' θ₁' σcap ρcap₁ ρcap₂
  have htransport : motive₂ σcap ρcap₀ ρcap₁ hcap :=
    agreeCapturedEnv.rec (predSat := predSat) (R := R) (μ₁ := μ₀) (μ₂ := μ₁) (θ₁ := θ₀) (θ₂ := θ₁)
      (motive_1 := motive₁) (motive_2 := motive₂)
      (clean_eq_nonref_nonarrow := by
        intro qt v₁ v₂ hpoison hnotfun hnotref hagree _hclean _hpred_compat₀ _hpred_compat₁ _hθ₀ _hθ₁
        exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison hnotfun hnotref hagree)
      (clean_internal_arrow := by
        intro st1 st2 p tcls qt tcl x body σcap ρcap₁ ρcap₂ v₁ v₂ hclean_internal hetyp htcl hmatch hcap
          hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ hv₁ hv₂ ihCap _hclean hpred_compat₀ hpred_compat₁ hθ₀ hθ₁
        exact agreeValueUnder.clean_internal_arrow hclean_internal hetyp htcl hmatch
          (ihCap hpred_compat₀ hpred_compat₁ hθ₀ hθ₁)
          (memberVarsRegimeEvidence_transport_μ hpred_compat₀ hmemberVars₁)
          (memberCvcrEvidence_transport_μ_θ hpred_compat₀ hθ₀ hmemberCvcr₁)
          (memberVarsRegimeEvidence_transport_μ hpred_compat₁ hmemberVars₂)
          (memberCvcrEvidence_transport_μ_θ hpred_compat₁ hθ₁ hmemberCvcr₂)
          hv₁ hv₂)
      (dirty_internal_arrow := by
        intro qt v₁ v₂ hdirty hisArrow htyp1 htyp2 _hclean _hpred_compat₀ _hpred_compat₁ hθ₀ hθ₁
        exact agreeValueUnder.dirty_internal_arrow hdirty hisArrow
          (valueHasETyp_extends hθ₀ htyp1) (valueHasETyp_extends hθ₁ htyp2))
      (clean_internal_parrow := by
        intro st1 st2 p tcls qt tcl x body pbody σcap ρcap₁ ρcap₂ v₁ v₂ hclean_internal hetyp htcl hmatch hcap
          hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ hv₁ hv₂ ihCap _hclean hpred_compat₀ hpred_compat₁ hθ₀ hθ₁
        exact agreeValueUnder.clean_internal_parrow hclean_internal hetyp htcl hmatch
          (ihCap hpred_compat₀ hpred_compat₁ hθ₀ hθ₁)
          (memberVarsRegimeEvidence_transport_μ hpred_compat₀ hmemberVars₁)
          (memberCvcrEvidence_transport_μ_θ hpred_compat₀ hθ₀ hmemberCvcr₁)
          (memberVarsRegimeEvidence_transport_μ hpred_compat₁ hmemberVars₂)
          (memberCvcrEvidence_transport_μ_θ hpred_compat₁ hθ₁ hmemberCvcr₂)
          hv₁ hv₂)
      (dirty_internal_parrow := by
        intro qt v₁ v₂ hdirty hisParrow htyp1 htyp2 _hclean _hpred_compat₀ _hpred_compat₁ hθ₀ hθ₁
        exact agreeValueUnder.dirty_internal_parrow hdirty hisParrow
          (valueHasETyp_extends hθ₀ htyp1) (valueHasETyp_extends hθ₁ htyp2))
      (clean_ref := by
        intro ls l a₁ a₂ qt v₁ v₂ hpoison hetyp hlookup1 hin hv1 hlookup2 hv2 _hclean _hpred_compat₀ _hpred_compat₁ hθ₀ hθ₁
        exact agreeValueUnder.clean_ref hpoison hetyp (hθ₀ _ _ hlookup1) hin hv1 (hθ₁ _ _ hlookup2) hv2)
      (withPred_true_eq := by
        intro k qt v₁ v₂ htag hregime hnotfun hnotref hagree _hclean _hpred_compat₀ _hpred_compat₁ _hθ₀ _hθ₁
        exact agreeValueUnder.withPred_true_eq k htag hregime hnotfun hnotref hagree)
      (withPred_true_ref := by
        intro k ls l a₁ a₂ qt v₁ v₂ htag hregime hetyp hlookup1 hin hv1 hlookup2 hv2 _hclean _hpred_compat₀ _hpred_compat₁ hθ₀ hθ₁
        exact agreeValueUnder.withPred_true_ref k htag hregime hetyp
          (hθ₀ _ _ hlookup1) hin hv1 (hθ₁ _ _ hlookup2) hv2)
      (nil := by
        intro ρcap₁ ρcap₂ _hpred_compat₀ _hpred_compat₁ _hθ₀ _hθ₁
        exact agreeCapturedEnv.nil)
      (cons_clean := by
        intro x qt σcap ρcap₁ ρcap₂ v₁ v₂ hclean hlookup1 hlookup2 htyp1 htyp2 hagree htail ihAgree ihTail
          hpred_compat₀ hpred_compat₁ hθ₀ hθ₁
        exact agreeCapturedEnv.cons_clean hclean hlookup1 hlookup2
          (valueHasETyp_extends hθ₀ htyp1) (valueHasETyp_extends hθ₁ htyp2)
          (ihAgree hclean hpred_compat₀ hpred_compat₁ hθ₀ hθ₁)
          (ihTail hpred_compat₀ hpred_compat₁ hθ₀ hθ₁))
      (cons_dirty := by
        intro x qt σcap ρcap₁ ρcap₂ v₁ v₂ hdirty hlookup1 hlookup2 htyp1 htyp2 htail ihTail
          hpred_compat₀ hpred_compat₁ hθ₀ hθ₁
        exact agreeCapturedEnv.cons_dirty hdirty hlookup1 hlookup2
          (valueHasETyp_extends hθ₀ htyp1) (valueHasETyp_extends hθ₁ htyp2)
          (ihTail hpred_compat₀ hpred_compat₁ hθ₀ hθ₁))
      hcap
  exact htransport hpred_compat₀ hpred_compat₁ hθ₀ hθ₁

-- Same-memory transport across realization-map extension. This is the Path D-safe
-- portion of `agreeValueUnder_clean_extends`.
lemma agreeValueUnder_clean_extends_sameMem
  {predSat : PredSat} {R : Regime} {μ₀ μ₁ : Memory}
  {θ₀ θ₁ θ₀' θ₁' : RealizationMap} {qt : QTyp} {v₀ v₁ : Value} :
  qtypCleanUnder R qt →
  θ₀.extendsMap θ₀' →
  θ₁.extendsMap θ₁' →
  agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ →
  agreeValueUnder predSat R μ₀ μ₁ θ₀' θ₁' qt v₀ v₁ := by
  intro hclean hθ₀ hθ₁ hagree
  exact agreeValueUnder_clean_extends
    (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) hclean hθ₀ hθ₁ hagree

-- Explicit memory-transport interface (with predicate-compatibility witnesses).
-- The current proof still delegates to the stronger selector-based lemma; this
-- wrapper is the call-site API we will keep when Path D removes selector
-- polymorphism.
lemma agreeValueUnder_clean_extends_transport_mem
  {predSat : PredSat} {R : Regime} {μ₀ μ₁ μ₀' μ₁' : Memory}
  {θ₀ θ₁ θ₀' θ₁' : RealizationMap} {qt : QTyp} {v₀ v₁ : Value}
  (_hpred_compat₀ : ∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ₀ v ↔ qtypPredHolds predSat qt μ₀' v)
  (_hpred_compat₁ : ∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ₁ v ↔ qtypPredHolds predSat qt μ₁' v) :
  qtypCleanUnder R qt →
  θ₀.extendsMap θ₀' →
  θ₁.extendsMap θ₁' →
  agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ →
  agreeValueUnder predSat R μ₀' μ₁' θ₀' θ₁' qt v₀ v₁ := by
  intro hclean hθ₀ hθ₁ hagree
  exact agreeValueUnder_clean_extends _hpred_compat₀ _hpred_compat₁ hclean hθ₀ hθ₁ hagree

lemma agreeCapturedEnv_clean_extends_sameMem
  {predSat : PredSat} {R : Regime} {μ₀ μ₁ : Memory}
  {θ₀ θ₁ θ₀' θ₁' : RealizationMap} {σcap : CapturedVarEnv} {ρcap₀ ρcap₁ : VarEnv} :
  θ₀.extendsMap θ₀' →
  θ₁.extendsMap θ₁' →
  agreeCapturedEnv predSat R μ₀ μ₁ θ₀ θ₁ σcap ρcap₀ ρcap₁ →
  agreeCapturedEnv predSat R μ₀ μ₁ θ₀' θ₁' σcap ρcap₀ ρcap₁ := by
  intro hθ₀ hθ₁ hcap
  exact agreeCapturedEnv_clean_extends
    (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) hθ₀ hθ₁ hcap

lemma agreeCapturedEnv_clean_extends_transport_mem
  {predSat : PredSat} {R : Regime} {μ₀ μ₁ μ₀' μ₁' : Memory}
  {θ₀ θ₁ θ₀' θ₁' : RealizationMap} {σcap : CapturedVarEnv} {ρcap₀ ρcap₁ : VarEnv}
  (_hpred_compat₀ : ∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ₀ v ↔ qtypPredHolds predSat qt μ₀' v)
  (_hpred_compat₁ : ∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ₁ v ↔ qtypPredHolds predSat qt μ₁' v) :
  θ₀.extendsMap θ₀' →
  θ₁.extendsMap θ₁' →
  agreeCapturedEnv predSat R μ₀ μ₁ θ₀ θ₁ σcap ρcap₀ ρcap₁ →
  agreeCapturedEnv predSat R μ₀' μ₁' θ₀' θ₁' σcap ρcap₀ ρcap₁ := by
  intro hθ₀ hθ₁ hcap
  exact agreeCapturedEnv_clean_extends _hpred_compat₀ _hpred_compat₁ hθ₀ hθ₁ hcap

lemma agreeCapturedEnv_of_agreeOnClean_aux
  (predSat : PredSat) (R : Regime) (ctx : TypeContext)
  (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ θ₁ : RealizationMap) (σcap : CapturedVarEnv) :
  runtimeInstantiatesCtx ctx μ₀ ρ₀ θ₀ →
  runtimeInstantiatesCtx ctx μ₁ ρ₁ θ₁ →
  agreeOnClean predSat R ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ →
  (∀ x qt, (x, qt) ∈ σcap → ctx.varEnv.lookup x = some qt) →
  agreeCapturedEnv predSat R μ₀ μ₁ θ₀ θ₁ σcap ρ₀ ρ₁ := by
  intro hric₀ hric₁ hagree
  rcases hric₀ with ⟨_hmem₀, hvars₀⟩
  rcases hric₁ with ⟨_hmem₁, hvars₁⟩
  rcases hagree with ⟨_hlocs, hvarsAg⟩
  induction σcap with
  | nil =>
      intro _hσlookup
      exact agreeCapturedEnv.nil
  | cons entry tail ih =>
      intro hσlookup
      rcases entry with ⟨x, qt⟩
      have hσlookup_tail : ∀ x qt, (x, qt) ∈ tail → ctx.varEnv.lookup x = some qt := by
        intro x qt hx
        exact hσlookup x qt (by simp [hx])
      by_cases hclean : qtypCleanUnder R qt
      · have hctx_lookup : ctx.varEnv.lookup x = some qt :=
          hσlookup x qt (by simp)
        have hvarEntry : agreeVarUnder predSat R μ₀ ρ₀ μ₁ ρ₁ θ₀ θ₁ (x, qt) :=
          hvarsAg x qt hctx_lookup hclean
        obtain ⟨v₀, hlookup₀, htyp₀⟩ := hvars₀ hctx_lookup
        obtain ⟨v₁, hlookup₁, htyp₁⟩ := hvars₁ hctx_lookup
        have hagreeVal : agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ :=
          agreeValueUnder_of_agreeVarUnder hvarEntry hlookup₀ hlookup₁
        exact agreeCapturedEnv.cons_clean hclean hlookup₀ hlookup₁ htyp₀ htyp₁ hagreeVal (ih hσlookup_tail)
      · have hctx_lookup : ctx.varEnv.lookup x = some qt :=
          hσlookup x qt (by simp)
        obtain ⟨v₀, hlookup₀, htyp₀⟩ := hvars₀ hctx_lookup
        obtain ⟨v₁, hlookup₁, htyp₁⟩ := hvars₁ hctx_lookup
        exact agreeCapturedEnv.cons_dirty hclean hlookup₀ hlookup₁ htyp₀ htyp₁ (ih hσlookup_tail)

lemma agreeCapturedEnv_of_agreeOnClean
  (predSat : PredSat) (R : Regime) (ctx : TypeContext)
  (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ θ₁ : RealizationMap) :
  runtimeInstantiatesCtx ctx μ₀ ρ₀ θ₀ →
  runtimeInstantiatesCtx ctx μ₁ ρ₁ θ₁ →
  agreeOnClean predSat R ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ →
  agreeCapturedEnv predSat R μ₀ μ₁ θ₀ θ₁ (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ ρ₁ := by
  intro hric₀ hric₁ hagree
  refine
    agreeCapturedEnv_of_agreeOnClean_aux predSat R ctx μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ (VarTypeEnv.toCaptured ctx.varEnv)
      hric₀ hric₁ hagree ?_
  intro x qt hmem
  have hmem' : (x, qt) ∈ ctx.varEnv.toList := by
    simpa [VarTypeEnv.toCaptured] using hmem
  have hget : ctx.varEnv[x]? = some qt :=
    (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some).1 hmem'
  simpa [VarTypeEnv.lookup, ExtTreeMap.get?_eq_getElem?] using hget

lemma agreeCapturedEnv_lookup_typed
  {predSat : PredSat} {R : Regime}
  {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
  {σcap : CapturedVarEnv} {ρcap₀ ρcap₁ : VarEnv}
  {y : Name} {qt : QTyp}
  (hcap : agreeCapturedEnv predSat R μ₀ μ₁ θ₀ θ₁ σcap ρcap₀ ρcap₁)
  (hlookup : σcap.lookup y = some qt) :
  ∃ v₀ v₁,
    ρcap₀.lookup y = some v₀ ∧
    valueHasETyp θ₀ v₀ qt.etyp ∧
    ρcap₁.lookup y = some v₁ ∧
    valueHasETyp θ₁ v₁ qt.etyp := by
  revert y qt hlookup
  induction σcap generalizing ρcap₀ ρcap₁ with
  | nil =>
      intro y qt hlookup
      cases hcap with
      | nil =>
          simp [CapturedVarEnv.lookup_eq, List.lookup] at hlookup
  | cons entry σtail ih =>
      intro y qt hlookup
      rcases entry with ⟨x, qtHead⟩
      cases hcap with
      | cons_clean hclean hlookup₀ hlookup₁ htyp₀ htyp₁ _hagree htail =>
          by_cases hyx : y == x
          · simp [CapturedVarEnv.lookup_eq, List.lookup, hyx] at hlookup
            have hyx' : y = x := beq_iff_eq.mp hyx
            subst hyx'
            cases hlookup
            exact ⟨_, _, hlookup₀, htyp₀, hlookup₁, htyp₁⟩
          · simp [CapturedVarEnv.lookup_eq, List.lookup, hyx] at hlookup
            exact ih (hcap := htail) hlookup
      | cons_dirty hdirty hlookup₀ hlookup₁ htyp₀ htyp₁ htail =>
          by_cases hyx : y == x
          · simp [CapturedVarEnv.lookup_eq, List.lookup, hyx] at hlookup
            have hyx' : y = x := beq_iff_eq.mp hyx
            subst hyx'
            cases hlookup
            exact ⟨_, _, hlookup₀, htyp₀, hlookup₁, htyp₁⟩
          · simp [CapturedVarEnv.lookup_eq, List.lookup, hyx] at hlookup
            exact ih (hcap := htail) hlookup

lemma agreeCapturedEnv_ofCaptured_lookup_typed_left
  {predSat : PredSat} {R : Regime}
  {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
  {σcap : CapturedVarEnv} {ρcap₀ ρcap₁ : VarEnv}
  (hcap : agreeCapturedEnv predSat R μ₀ μ₁ θ₀ θ₁ σcap ρcap₀ ρcap₁) :
  ∀ y qt, (VarTypeEnv.ofCaptured σcap).lookup y = some qt →
    ∃ v, ρcap₀.lookup y = some v ∧ valueHasETyp θ₀ v qt.etyp := by
  intro y qt hlookup
  have hlist : σcap.lookup y = some qt :=
    list_lookup_of_ofCaptured_lookup σcap y qt hlookup
  rcases agreeCapturedEnv_lookup_typed hcap hlist with ⟨v₀, _v₁, hlookup₀, htyp₀, _hlookup₁, _htyp₁⟩
  exact ⟨v₀, hlookup₀, htyp₀⟩

lemma agreeCapturedEnv_ofCaptured_lookup_typed_right
  {predSat : PredSat} {R : Regime}
  {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
  {σcap : CapturedVarEnv} {ρcap₀ ρcap₁ : VarEnv}
  (hcap : agreeCapturedEnv predSat R μ₀ μ₁ θ₀ θ₁ σcap ρcap₀ ρcap₁) :
  ∀ y qt, (VarTypeEnv.ofCaptured σcap).lookup y = some qt →
    ∃ v, ρcap₁.lookup y = some v ∧ valueHasETyp θ₁ v qt.etyp := by
  intro y qt hlookup
  have hlist : σcap.lookup y = some qt :=
    list_lookup_of_ofCaptured_lookup σcap y qt hlookup
  rcases agreeCapturedEnv_lookup_typed hcap hlist with ⟨_v₀, v₁, _hlookup₀, _htyp₀, hlookup₁, htyp₁⟩
  exact ⟨v₁, hlookup₁, htyp₁⟩

lemma agreeCapturedEnv_lookup_agreeVarUnder_clean
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

lemma RealizationMap_lookup_update_ne
  {θ : RealizationMap} {l l' : Loc} {addr : Address} :
  l' ≠ l →
  (θ.update l addr).lookup l' = θ.lookup l' := by
  intro hne
  have hcmp : compare l l' ≠ Ordering.eq := by
    intro hcmp
    have : l = l' := LawfulEqCmp.eq_of_compare hcmp
    exact hne this.symm
  simp [RealizationMap.update, RealizationMap.lookup, ExtTreeMap.getElem?_insert, hcmp]

lemma Memory_lookup_update_ne
  {μ : Memory} {a a' : Address} {v : Int} :
  a ≠ a' →
  (Memory.update μ a' v).lookup a = μ.lookup a := by
  intro hne
  have hcmp : compare a' a ≠ Ordering.eq := by
    intro hcmp
    have : a' = a := LawfulEqCmp.eq_of_compare hcmp
    exact hne this.symm
  simp [Memory.update, Memory.lookup, ExtTreeMap.getElem?_insert, hcmp]

lemma Memory_contains_of_lookup {μ : Memory} {a : Address} {n : Int} :
  Memory.lookup μ a = some n →
  μ.contains a = true := by
  intro hlookup
  have hisSome : μ[a]?.isSome = true := by
    have h' : μ[a]? = some n := by
      simpa [Memory.lookup, ExtTreeMap.get?_eq_getElem?] using hlookup
    simp [h']
  have hmem : a ∈ μ := (ExtTreeMap.mem_iff_isSome_getElem?).2 hisSome
  exact (ExtTreeMap.contains_iff_mem).2 hmem

lemma Memory_lookup_some_of_contains {μ : Memory} {a : Address} :
  μ.contains a = true →
  ∃ n, Memory.lookup μ a = some n := by
  intro hcontains
  have hmem : a ∈ μ := (ExtTreeMap.contains_iff_mem).1 hcontains
  have hisSome : μ[a]?.isSome = true := (ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
  cases hlookup : μ[a]? with
  | none =>
      simp [hlookup] at hisSome
  | some n =>
      exact ⟨n, by simp [Memory.lookup, ExtTreeMap.get?_eq_getElem?, hlookup]⟩

lemma agreeOnClean_newRef_extend
  (predSat : PredSat) (R : Regime) (ctxᵢ : TypeContext)
  (res1 res : TypeResult) (l : Loc) (etyp : ETyp)
  (cfg₀' cfg₁' cf₀ cf₁ : Config) (n₀ n₁ : Int) (a₀_new a₁_new : Address)
  (θ₀1 θ₁1 θ₀' θ₁' : RealizationMap)
  (h_mem :
      res.memEnv' =
        updateMemEnv res1.memEnv' l
          ⟨etyp, joinPoison ctxᵢ.pc res1.qualType.poison,
            if ctxᵢ.pc = true then Predicate.noPred else res1.qualType.pred⟩)
  (h_etyp1 : res1.qualType.etyp = etyp)
  (h_etyp_int : etyp = ETyp.int)
  (ha₀_new : a₀_new = cfg₀'.nextAddr)
  (ha₁_new : a₁_new = cfg₁'.nextAddr)
  (hmem₀ : cf₀.memory = cfg₀'.memory.update a₀_new n₀)
  (hmem₁ : cf₁.memory = cfg₁'.memory.update a₁_new n₁)
  (hvar₀ : cf₀.varEnv = cfg₀'.varEnv)
  (hvar₁ : cf₁.varEnv = cfg₁'.varEnv)
  (hθ₀def : θ₀' = θ₀1.update l a₀_new)
  (hθ₁def : θ₁' = θ₁1.update l a₁_new)
  (hθext₀' : wfExtendsMap θ₀1 θ₀')
  (hθext₁' : wfExtendsMap θ₁1 θ₁')
  (hwfcf₀1 : wfConfig cfg₀')
  (hwfcf₁1 : wfConfig cfg₁')
  (hqtypPredHolds_mem₀ :
      ∀ (qt : QTyp) (v : Value),
        qtypPredHolds predSat qt cfg₀'.memory v ↔ qtypPredHolds predSat qt cf₀.memory v)
  (hqtypPredHolds_mem₁ :
      ∀ (qt : QTyp) (v : Value),
        qtypPredHolds predSat qt cfg₁'.memory v ↔ qtypPredHolds predSat qt cf₁.memory v)
  (hagree_clean_e :
      agreeOnClean predSat R (ctxAfter ctxᵢ res1)
        cfg₀'.memory cfg₀'.varEnv θ₀1 cfg₁'.memory cfg₁'.varEnv θ₁1)
  (hres_agree_e :
      resultAgreesIfClean predSat R cfg₀'.memory cfg₁'.memory θ₀1 θ₁1 res1.qualType (Value.num n₀) (Value.num n₁)) :
  agreeOnClean predSat R (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' cf₁.memory cf₁.varEnv θ₁' := by
  let storedQt : QTyp :=
    ⟨etyp, joinPoison ctxᵢ.pc res1.qualType.poison,
      if ctxᵢ.pc = true then Predicate.noPred else res1.qualType.pred⟩
  constructor
  · intro l' qt hlookup hclean
    by_cases h_eq : l' = l
    · subst l'
      have hqt : qt = storedQt := by
        have hlookup' : res.memEnv'.lookup l = some qt := by
          simpa [ctxAfter] using hlookup
        rw [h_mem] at hlookup'
        have hself : (updateMemEnv res1.memEnv' l storedQt).lookup l = some storedQt := by
          simp only [updateMemEnv, storedQt, MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?,
            Std.ExtTreeMap.getElem?_insert_self, Option.map, h_etyp_int]
        have : (some qt : Option QTyp) = some storedQt := by
          calc
            some qt = (updateMemEnv res1.memEnv' l storedQt).lookup l := by symm; exact hlookup'
            _ = some storedQt := by exact hself
        exact Option.some.inj this
      subst hqt
      have hreal0 : θ₀'.lookup l = some a₀_new := by
        rw [hθ₀def]
        simp [RealizationMap.update, RealizationMap.lookup]
      have hreal1 : θ₁'.lookup l = some a₁_new := by
        rw [hθ₁def]
        simp [RealizationMap.update, RealizationMap.lookup]
      have hlookup0 : cf₀.memory.lookup a₀_new = some n₀ := by
        rw [hmem₀]
        simp [Memory.update, Memory.lookup]
      have hlookup1 : cf₁.memory.lookup a₁_new = some n₁ := by
        rw [hmem₁]
        simp [Memory.update, Memory.lookup]
      have hclean_res1 : qtypCleanUnder R res1.qualType := by
        cases hclean with
        | clean hpoison =>
            have hjoin : joinPoison ctxᵢ.pc res1.qualType.poison = false := by
              simpa [storedQt] using hpoison
            exact qtypCleanUnder.clean (joinPoison_eq_false hjoin).2
        | guard k htag hreg hnotfun =>
            have hpc_false : ctxᵢ.pc = false := by
              cases hpc : ctxᵢ.pc with
              | false => exact rfl
              | true =>
                  simp [storedQt, qtypGuardTag, hpc] at htag
            have htag' : qtypGuardTag res1.qualType = some k := by
              simpa [qtypGuardTag, storedQt, hpc_false] using htag
            have hnotfun' : res1.qualType.etyp.isFunctionType = false := by
              simpa [storedQt, h_etyp1] using hnotfun
            exact qtypCleanUnder.guard k htag' hreg hnotfun'
      have hagree_res1 :
          agreeValueUnder predSat R cfg₀'.memory cfg₁'.memory θ₀1 θ₁1 res1.qualType (Value.num n₀) (Value.num n₁) :=
        hres_agree_e hclean_res1
      have hagree_stored_old :
          agreeValueUnder predSat R cfg₀'.memory cfg₁'.memory θ₀1 θ₁1 storedQt (Value.num n₀) (Value.num n₁) := by
        refine agreeValueUnder_transport_clean hclean ?_ ?_ hagree_res1
        · simp [storedQt, h_etyp1]
        · intro hpoison
          have hjoin : joinPoison ctxᵢ.pc res1.qualType.poison = false := by
            simpa [storedQt] using hpoison
          exact (joinPoison_eq_false hjoin).2
      have hagree_stored :
          agreeValueUnder predSat R cf₀.memory cf₁.memory θ₀' θ₁' storedQt (Value.num n₀) (Value.num n₁) :=
        agreeValueUnder_clean_extends_transport_mem
          hqtypPredHolds_mem₀ hqtypPredHolds_mem₁ hclean hθext₀'.1 hθext₁'.1 hagree_stored_old
      exact agreeLocUnder.agree_values l storedQt a₀_new a₁_new n₀ n₁ hreal0 hreal1 hlookup0 hlookup1 hagree_stored
    · have hlookup_old : (ctxAfter ctxᵢ res1).memEnv.lookup l' = some qt := by
        have hlookup' : res.memEnv'.lookup l' = some qt := by
          simpa [ctxAfter] using hlookup
        rw [h_mem] at hlookup'
        have hEq :
            (updateMemEnv res1.memEnv' l storedQt).lookup l' = res1.memEnv'.lookup l' :=
          MemoryTypeEnv_lookup_updateMemEnv_ne (Γ := res1.memEnv') (l := l) (l' := l') (qt := storedQt) h_eq
        have hlookup_old' : res1.memEnv'.lookup l' = some qt := by
          have htmp := hlookup'
          rw [hEq] at htmp
          exact htmp
        simpa [ctxAfter] using hlookup_old'
      have hagree_old := hagree_clean_e.1 l' qt hlookup_old hclean
      cases hagree_old with
      | both_unrealized _ _ hnone0 hnone1 =>
          have hnone0' : θ₀'.lookup l' = none := by
            rw [hθ₀def]
            simpa [RealizationMap_lookup_update_ne (θ := θ₀1) (l := l) (l' := l') (addr := a₀_new) h_eq] using hnone0
          have hnone1' : θ₁'.lookup l' = none := by
            rw [hθ₁def]
            simpa [RealizationMap_lookup_update_ne (θ := θ₁1) (l := l) (l' := l') (addr := a₁_new) h_eq] using hnone1
          exact agreeLocUnder.both_unrealized l' qt hnone0' hnone1'
      | agree_values _ _ a0 a1 m0 m1 hreal0 hreal1 hm0 hm1 hagree =>
          have hne0 : a0 ≠ a₀_new := by
            intro hcontra
            have hcontains : cfg₀'.memory.contains a₀_new := by
              have : cfg₀'.memory.contains a0 := Memory_contains_of_lookup hm0
              simpa [hcontra] using this
            have hlt : a₀_new < cfg₀'.nextAddr := hwfcf₀1.1 a₀_new (by simpa using hcontains)
            have : cfg₀'.nextAddr < cfg₀'.nextAddr := by simp [ha₀_new] at hlt
            exact Nat.lt_irrefl cfg₀'.nextAddr this
          have hne1 : a1 ≠ a₁_new := by
            intro hcontra
            have hcontains : cfg₁'.memory.contains a₁_new := by
              have : cfg₁'.memory.contains a1 := Memory_contains_of_lookup hm1
              simpa [hcontra] using this
            have hlt : a₁_new < cfg₁'.nextAddr := hwfcf₁1.1 a₁_new (by simpa using hcontains)
            have : cfg₁'.nextAddr < cfg₁'.nextAddr := by simp [ha₁_new] at hlt
            exact Nat.lt_irrefl cfg₁'.nextAddr this
          have hreal0' : θ₀'.lookup l' = some a0 := by
            rw [hθ₀def]
            simpa [RealizationMap_lookup_update_ne (θ := θ₀1) (l := l) (l' := l') (addr := a₀_new) h_eq] using hreal0
          have hreal1' : θ₁'.lookup l' = some a1 := by
            rw [hθ₁def]
            simpa [RealizationMap_lookup_update_ne (θ := θ₁1) (l := l) (l' := l') (addr := a₁_new) h_eq] using hreal1
          have hm0' : cf₀.memory.lookup a0 = some m0 := by
            rw [hmem₀]
            have hEq :=
              Memory_lookup_update_ne (μ := cfg₀'.memory) (a := a0) (a' := a₀_new) (v := n₀) hne0
            simpa [hEq] using hm0
          have hm1' : cf₁.memory.lookup a1 = some m1 := by
            rw [hmem₁]
            have hEq :=
              Memory_lookup_update_ne (μ := cfg₁'.memory) (a := a1) (a' := a₁_new) (v := n₁) hne1
            simpa [hEq] using hm1
          have hagree' :
              agreeValueUnder predSat R cf₀.memory cf₁.memory θ₀' θ₁' qt (Value.num m0) (Value.num m1) :=
            agreeValueUnder_clean_extends_transport_mem
              hqtypPredHolds_mem₀ hqtypPredHolds_mem₁ hclean hθext₀'.1 hθext₁'.1 hagree
          exact agreeLocUnder.agree_values l' qt a0 a1 m0 m1 hreal0' hreal1' hm0' hm1' hagree'
  · intro x qt hlookup hclean
    have hlookup_old : (ctxAfter ctxᵢ res1).varEnv.lookup x = some qt := by
      simpa [ctxAfter] using hlookup
    have hagree_old := hagree_clean_e.2 x qt hlookup_old hclean
    cases hagree_old with
    | both_none _ _ hnone0 hnone1 =>
        refine agreeVarUnder.both_none x qt ?_ ?_
        · simpa [hvar₀] using hnone0
        · simpa [hvar₁] using hnone1
    | agree_values _ _ v0 v1 hlook0 hlook1 hagree =>
        have hagree' :
            agreeValueUnder predSat R cf₀.memory cf₁.memory θ₀' θ₁' qt v0 v1 :=
          agreeValueUnder_clean_extends_transport_mem
            hqtypPredHolds_mem₀ hqtypPredHolds_mem₁ hclean hθext₀'.1 hθext₁'.1 hagree
        refine agreeVarUnder.agree_values x qt v0 v1 ?_ ?_ hagree'
        · simpa [hvar₀] using hlook0
        · simpa [hvar₁] using hlook1

lemma var_valueHasETyp_of_typecheck
  (ctx : TypeContext) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) (x : Name) (res : TypeResult) (o : Value)
  (htc : typecheckVar ctx x = .ok res)
  (hwfθ : wfRealizationMap θ)
  (hric : runtimeInstantiatesCtx ctx μ ρ θ)
  (hlookup : ρ.lookup x = some o) :
  valueHasETyp θ o res.qualType.etyp := by
  cases hlookup_ctx : ctx.varEnv.lookup x with
  | none =>
      simp [typecheckVar, hlookup_ctx] at htc
  | some qt =>
      obtain ⟨v, hv, htyp⟩ := var_has_correct_type ctx μ ρ θ x qt hwfθ hric hlookup_ctx
      have heq : v = o := Option.some.inj (hv.symm.trans hlookup)
      have hetyp : res.qualType.etyp = qt.etyp := by
        simp only [typecheckVar, hlookup_ctx] at htc
        (split at htc; try split at htc);
          repeat (first | split at htc | simp [pure, Except.pure] at htc | cases htc | rfl)
      rw [← heq, hetyp]; exact htyp

-- Transfer consistentWithRegime using monotoneStep
-- When Regime.monotoneStep R R', if consistentWithRegime holds for R, it holds for R'
-- (R' has fewer entries, so fewer constraints need to be checked)
lemma consistentWithRegime_monotone
    (predSat : PredSat) (R R' : Regime) (ctx : TypeContext)
    (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
    (h_mono : Regime.monotoneStep R R')
    (h_cwr : consistentWithRegime predSat R ctx μ ρ θ) :
    consistentWithRegime predSat R' ctx μ ρ θ := by
  simp only [consistentWithRegime] at h_cwr ⊢
  refine ⟨?_, ?_, ?_⟩
  · -- Location regime consistency
    intro l qt k hlookup hguard hR'def
    cases hk' : R'.lookup? k with
    | none => exact absurd hk' hR'def
    | some b =>
        have hRdef : R.lookup? k ≠ none := h_mono.2.2 k hR'def
        cases hk : R.lookup? k with
        | none => exact absurd hk hRdef
        | some b' =>
            have h := h_mono.2.1 k b' hk
            cases h with
            | inl h_eq =>
                have hb_eq : b' = b := by
                  have : some b' = some b := h_eq.symm.trans hk'
                  exact Option.some.inj this
                have hk_b : R.lookup? k = some b := by rw [← hb_eq]; exact hk
                have h_locsR := h_cwr.1 l qt k hlookup hguard hRdef
                exact locsRegime_monotone h_mono hguard hk_b hk' h_locsR
            | inr h_none =>
                simp [h_none] at hk'
  · -- Variable regime consistency (similar)
    intro x qt k hlookup hguard hR'def
    cases hk' : R'.lookup? k with
    | none => exact absurd hk' hR'def
    | some b =>
        have hRdef : R.lookup? k ≠ none := h_mono.2.2 k hR'def
        cases hk : R.lookup? k with
        | none => exact absurd hk hRdef
        | some b' =>
            have h := h_mono.2.1 k b' hk
            cases h with
            | inl h_eq =>
                have hb_eq : b' = b := by
                  have : some b' = some b := h_eq.symm.trans hk'
                  exact Option.some.inj this
                have hk_b : R.lookup? k = some b := by rw [← hb_eq]; exact hk
                have h_varsR := h_cwr.2.1 x qt k hlookup hguard hRdef
                exact varsRegime_monotone h_mono hguard hk_b hk' h_varsR
            | inr h_none =>
                simp [h_none] at hk'
  · -- Third conjunct: closureCapturedVarsRegime monotone under h_mono.
    intro x qt v hlookup hρ
    exact closureCapturedVarsRegime_monotone h_mono (h_cwr.2.2 x qt v hlookup hρ)

lemma opEType_ne_ref (op : Op) (et1 et2 : ETyp) (ls : LocSet) :
  opEType? op et1 et2 ≠ some (ETyp.ref ls) := by
  cases op <;> cases et1 <;> cases et2 <;> simp [opEType?]

lemma opEType_implies_nonfun (op : Op) (et1 et2 result : ETyp) :
  opEType? op et1 et2 = some result →
  et1.isFunctionType = false ∧ et2.isFunctionType = false ∧ result.isFunctionType = false := by
  intro h
  cases op <;> cases et1 <;> cases et2 <;> simp [opEType?] at h <;> cases h <;>
    simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]

lemma opUnaryEType_ne_ref (op : UnaryOp) (et1 : ETyp) (ls : LocSet) :
  opUnaryEType? op et1 ≠ some (ETyp.ref ls) := by
  cases op
  cases et1 <;> simp [opUnaryEType?]

lemma opUnaryEType_implies_nonfun (op : UnaryOp) (et1 result : ETyp) :
  opUnaryEType? op et1 = some result →
  et1.isFunctionType = false ∧ result.isFunctionType = false := by
  intro h
  cases op with
  | not =>
      cases et1 with
      | int =>
          cases h
      | bool =>
          cases h
          simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
      | unit =>
          cases h
      | string =>
          cases h
      | ref ls =>
          cases h
      | arrow st1 st2 p tcls =>
          cases h
      | parrow st1 st2 p tcls =>
          cases h

-- When evalOp succeeds and OpEType fixes the result type, the value has that type
lemma valueHasETyp_of_evalOp
  (op : Op) (v1 v2 v : Value) (θ : RealizationMap) (t1 t2 result_etyp : ETyp)
  (hop : OpEType op t1 t2 result_etyp)
  (heval : LeanPoison.evalOp op v1 v2 = some v) :
  valueHasETyp θ v result_etyp := by
  cases hop <;> simp only [LeanPoison.evalOp] at heval <;> cases v1 <;> cases v2 <;> simp at heval <;> cases heval
  · exact valueHasETyp.num _
  · exact valueHasETyp.num _
  · exact valueHasETyp.num _
  · exact valueHasETyp.num _
  · exact valueHasETyp.bool _
  · exact valueHasETyp.bool _
  · exact valueHasETyp.bool _
  · exact valueHasETyp.bool _
  · exact valueHasETyp.bool _
  · exact valueHasETyp.bool _
  · exact valueHasETyp.bool _
  · exact valueHasETyp.bool _
  · exact valueHasETyp.num _

-- When evalUnaryOp succeeds and opUnaryEType? fixes the result type, the value has that type
lemma valueHasETyp_of_evalUnaryOp
  (op : UnaryOp) (v1 v : Value) (θ : RealizationMap) (t1 result_etyp : ETyp)
  (hop : opUnaryEType? op t1 = some result_etyp)
  (heval : LeanPoison.evalUnaryOp op v1 = some v) :
  valueHasETyp θ v result_etyp := by
  (cases op; simp [opUnaryEType?] at hop)
  cases t1 <;> simp at hop
  cases hop
  simp only [LeanPoison.evalUnaryOp] at heval
  cases v1 <;> simp at heval
  cases heval
  exact valueHasETyp.bool _

abbrev StepFR_IH (predSat : PredSat) (tm : TagMeaning) (fuel : Nat) : Prop :=
  ∀ m < fuel, ∀ (e : Expr) (ctxᵢ : TypeContext),
    wfTagMeaningCtx tm ctxᵢ →
    ∀ (res : TypeResult), typecheck .ioFree ctxᵢ e m = .ok res → StepFR .ioFree ctxᵢ e res predSat tm

abbrev StepFRSingleRunFinalCleanPcTrue_IH
    (predSat : PredSat) (tm : TagMeaning) (fuel : Nat) : Prop :=
  ∀ m < fuel, ∀ (e : Expr) (ctxᵢ : TypeContext),
    wfTagMeaningCtx tm ctxᵢ →
    ∀ (res : TypeResult),
      typecheck .ioFree ctxᵢ e m = .ok res →
      StepFRSingleRunFinalCleanPcTrue .ioFree ctxᵢ e res predSat tm

-- Convert strong-induction IH (no wfTagMeaningCtx) to StepFR_IH; the extra premise is unused
lemma StepFR_IH_of_induction
  (predSat : PredSat) (tm : TagMeaning) (k : Nat)
  (IH : ∀ m < k, ∀ (e : Expr) (ctxᵢ : TypeContext) (res : TypeResult),
    typecheck .ioFree ctxᵢ e m = .ok res → StepFR .ioFree ctxᵢ e res predSat tm) :
  StepFR_IH predSat tm k :=
  fun m hm e ctxᵢ _hwfTm res htc => IH m hm e ctxᵢ res htc

lemma StepFRSingleRunFinalCleanPcTrue_IH_of_induction
  (predSat : PredSat) (tm : TagMeaning) (k : Nat)
  (IH : ∀ m < k, ∀ (e : Expr) (ctxᵢ : TypeContext) (res : TypeResult),
    typecheck .ioFree ctxᵢ e m = .ok res →
      StepFRSingleRunFinalCleanPcTrue .ioFree ctxᵢ e res predSat tm) :
  StepFRSingleRunFinalCleanPcTrue_IH predSat tm k :=
  fun m hm e ctxᵢ _hwfTm res htc => IH m hm e ctxᵢ res htc

end TypeSystemEnforcesFaultRobustness_step_proof

-- Moved from IOFree section: used by both stepFR_ite and stepFR_app
lemma agreeValueUnder_clean_transport_by_cleanBack
    {predSat : PredSat} {R R' : Regime}
    {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
    {qt : QTyp} {v₀ v₁ : Value}
    (h_clean_back : ∀ qt, qtypCleanUnder R' qt → qtypCleanUnder R qt)
    (hmemberVars₀_transport :
      ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
        MemberVarsRegimeEvidence predSat R μ₀ σcap ρcap →
          MemberVarsRegimeEvidence predSat R' μ₀ σcap ρcap)
    (hmemberCvcr₀_transport :
      ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
        MemberCvcrEvidence predSat R μ₀ θ₀ σcap ρcap →
          MemberCvcrEvidence predSat R' μ₀ θ₀ σcap ρcap)
    (hmemberVars₁_transport :
      ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
        MemberVarsRegimeEvidence predSat R μ₁ σcap ρcap →
          MemberVarsRegimeEvidence predSat R' μ₁ σcap ρcap)
    (hmemberCvcr₁_transport :
      ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
        MemberCvcrEvidence predSat R μ₁ θ₁ σcap ρcap →
          MemberCvcrEvidence predSat R' μ₁ θ₁ σcap ρcap) :
    qtypCleanUnder R' qt →
      agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ →
        agreeValueUnder predSat R' μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ := by
  intro hclean hagree
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
          hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁ hv₀ hv₁ ihcap
          _hclean
        exact agreeValueUnder.clean_internal_arrow hclean_internal hetyp htcl hmatch ihcap
          (hmemberVars₀_transport hmemberVars₀)
          (hmemberCvcr₀_transport hmemberCvcr₀)
          (hmemberVars₁_transport hmemberVars₁)
          (hmemberCvcr₁_transport hmemberCvcr₁)
          hv₀ hv₁)
      (dirty_internal_arrow := by
        intro qt v₀ v₁ hdirty_internal hisArrow htyp1 htyp2 _hclean
        exact agreeValueUnder.dirty_internal_arrow hdirty_internal hisArrow htyp1 htyp2)
      (clean_internal_parrow := by
        intro st1 st2 p tcls qt tcl x body pbody σcap ρcap₀ ρcap₁ v₀ v₁ hclean_internal hetyp htcl hmatch hcap
          hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁ hv₀ hv₁ ihcap
          _hclean
        exact agreeValueUnder.clean_internal_parrow hclean_internal hetyp htcl hmatch ihcap
          (hmemberVars₀_transport hmemberVars₀)
          (hmemberCvcr₀_transport hmemberCvcr₀)
          (hmemberVars₁_transport hmemberVars₁)
          (hmemberCvcr₁_transport hmemberCvcr₁)
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
          exact hdirty (h_clean_back qt hcleanR')
        exact agreeCapturedEnv.cons_dirty hdirty' hlookup1 hlookup2 htyp1 htyp2 ihtail)
      hagree
  exact hrec hclean

-- World-free version of ite fault-robustness
-- Proof structure follows typecheckIf's 4 modes:
-- Mode 1: R(k) = some true - commits to then-branch (e2)
--   Key: uses consistentWithRegime + PredSatLaws.match_iff to show both runs take then-branch
-- Mode 2: R(k) = some false - commits to else-branch (e3)
--   Key: symmetric to mode 1
-- Mode 3: R(k) = none - conservative join of both branches
--   Requires case analysis on which branch each run actually takes
-- Mode 4: matchGuard fails - standard conservative join
--   Similar to mode 3
-- This proof was previously blocked by issue #98, now resolved by adding consistentWithRegime

-- Mode 1: R(k) = some true (then-branch effective)


-- Moved from StepFRApp: shared typecheck preservation lemmas for tag meaning/regime consistency.
lemma applyFnTClosure_regular_structure
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate) (result2 : TypeResult) (fuel : Nat)
  (x : Name) (body : Expr) (tenv : CapturedVarEnv)
  (first : TypeResult)
  (_happly : applyFnTClosure .ioFree (FnTClosure.regular x body tenv) st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel = .ok first) :
  ∃ fuelBody, fuel = Nat.succ fuelBody := by
  cases fuel with
  | zero =>
      simp [applyFnTClosure] at _happly
  | succ fuelBody =>
      exact ⟨fuelBody, rfl⟩

-- In ioFree mode, extern closure application always throws (so cannot occur in stepFR_app).
lemma applyFnTClosure_ioFree_extern_fails
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuel : Nat)
  (x : Name) (retSpec : ExternReturn) (effects : List Effect) (capturedEnv : CapturedVarEnv)
  (r : TypeResult) :
  applyFnTClosure .ioFree (FnTClosure.extern x retSpec effects capturedEnv) st1 st2 p p1
    argEtyp argPoison argPred ctx result2 fuel ≠ .ok r := by
  intro h
  cases fuel with
  | zero =>
    unfold applyFnTClosure at h
    simp at h
  | succ _ =>
    unfold applyFnTClosure at h
    have hcond : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := rfl
    simp only [hcond, ite_true, bind, Except.bind] at h
    exact absurd h (Except.error_ne_ok "Extern function application forbidden in ioFree mode" r)

-- Inversion for regular closures: successful application exposes the body typing
-- derivation and successful return-type subtype check.
lemma applyFnTClosure_regular_inv
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuelBody : Nat)
  (x : Name) (body : Expr) (tenv : CapturedVarEnv)
  (first : TypeResult)
  (happly :
    applyFnTClosure .ioFree (FnTClosure.regular x body tenv) st1 st2 p p1
      argEtyp argPoison argPred ctx result2 (Nat.succ fuelBody) = .ok first) :
  ∃ result3,
    typecheckExpr .ioFree
      { ctx with
        pc := joinPoison p (joinPoison p1 ctx.pc)
        memEnv := result2.memEnv'
        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
          ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        tagEnv := result2.tagEnv'
        nextTag := result2.nextTag'
        nextLoc := result2.nextLoc'
        regime := result2.regime' } body fuelBody = .ok result3 ∧
    isSubtype st2 result3.qualType = true ∧
    first =
      { result3 with
        qualType :=
          normalizeAppResultByProvenance (joinPoison p1 p)
            { result3.qualType with poison := joinPoison p1 (joinPoison p result3.qualType.poison) } } := by
  unfold applyFnTClosure at happly
  simp [bind, Except.bind] at happly
  cases htc_body : typecheckExpr .ioFree
      { ctx with
        pc := joinPoison p (joinPoison p1 ctx.pc)
        memEnv := result2.memEnv'
        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
          ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        tagEnv := result2.tagEnv'
        nextTag := result2.nextTag'
        nextLoc := result2.nextLoc'
        regime := result2.regime' } body fuelBody with
  | error err =>
      simp [htc_body] at happly
  | ok result3 =>
      simp [htc_body] at happly
      cases hsub : isSubtype st2 result3.qualType with
      | false =>
          cases hq3 : result3.qualType with
          | mk et3 p3 pred3 =>
              have hsub' : isSubtype st2 { etyp := et3, poison := p3, pred := pred3 } = false := by
                simpa [hq3] using hsub
              simp [hq3, hsub'] at happly
      | true =>
          cases hq3 : result3.qualType with
          | mk et3 p3 pred3 =>
              have hsub' : isSubtype st2 { etyp := et3, poison := p3, pred := pred3 } = true := by
                simpa [hq3] using hsub
              have happly' :
                  (Except.ok first : Except String TypeResult) =
                    Except.ok
                      { result3 with
                        qualType :=
                          normalizeAppResultByProvenance (joinPoison p1 p)
                            { result3.qualType with
                              poison := joinPoison p1 (joinPoison p result3.qualType.poison) } } := by
                simpa [hq3, hsub', pure, Except.pure] using happly.symm
              have hfirst :
                  first =
                    { result3 with
                      qualType :=
                        normalizeAppResultByProvenance (joinPoison p1 p)
                          { result3.qualType with
                            poison := joinPoison p1 (joinPoison p result3.qualType.poison) } } := by
                injection happly' with hEq
              exact ⟨result3, rfl, hsub, hfirst⟩

-- If `List.mapM f xs` succeeds and `x ∈ xs`, then `f x` succeeded for some output
-- appearing in the mapped result list.
lemma list_mapM_ok_mem_input_exists_output
  {α β ε : Type}
  (f : α → Except ε β) :
  ∀ {xs ys x}, List.mapM f xs = .ok ys → x ∈ xs →
    ∃ y, y ∈ ys ∧ f x = .ok y := by
  intro xs ys x hmap hmem
  have hforall2 : List.Forall₂ (fun x y => f x = Except.ok y) xs ys :=
    List.mapM_Except_ok_implies_forall2 xs f ys hmap
  rcases List.Forall2.exists_of_mem_left (R := fun x y => f x = Except.ok y) hforall2 x hmem with
    ⟨y, hy, hxy⟩
  exact ⟨y, hy, hxy⟩

-- Specialized extraction for closure-application maps used in `stepFR_app`.
lemma applyFnTClosure_ok_of_mem_mapM
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuel : Nat)
  (tcls : List FnTClosure) (results : List TypeResult) (tcl : FnTClosure)
  (hmap : List.mapM
      (fun tcl' => applyFnTClosure .ioFree tcl' st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel)
      tcls = .ok results)
  (hmem : tcl ∈ tcls) :
  ∃ r, r ∈ results ∧
    applyFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel = .ok r := by
  simpa using
    (list_mapM_ok_mem_input_exists_output
      (f := fun tcl' => applyFnTClosure .ioFree tcl' st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel)
      (xs := tcls) (ys := results) (x := tcl) hmap hmem)

-- Combined extraction for regular closures from a successful application map.
-- Gives the selected closure's successful application together with body-typing inversion.
lemma applyFnTClosure_regular_inv_of_mapM_mem
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (bodyState : TypeResult) (fuel : Nat)
  (tcls : List FnTClosure) (results : List TypeResult)
  (x : Name) (body : Expr) (tenv : CapturedVarEnv)
  (hmap : List.mapM
      (fun tcl' => applyFnTClosure .ioFree tcl' st1 st2 p p1 argEtyp argPoison argPred ctx bodyState fuel)
      tcls = .ok results)
  (hmem : FnTClosure.regular x body tenv ∈ tcls) :
  ∃ fuelBody first result3,
    applyFnTClosure .ioFree (FnTClosure.regular x body tenv) st1 st2 p p1
      argEtyp argPoison argPred ctx bodyState fuel = .ok first ∧
    fuel = Nat.succ fuelBody ∧
    typecheckExpr .ioFree
      { ctx with
        pc := joinPoison p (joinPoison p1 ctx.pc)
        memEnv := bodyState.memEnv'
        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
          ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        tagEnv := bodyState.tagEnv'
        nextTag := bodyState.nextTag'
        nextLoc := bodyState.nextLoc'
        regime := bodyState.regime' } body fuelBody = .ok result3 ∧
    isSubtype st2 result3.qualType = true ∧
    first =
      { result3 with
        qualType :=
          normalizeAppResultByProvenance (joinPoison p1 p)
            { result3.qualType with poison := joinPoison p1 (joinPoison p result3.qualType.poison) } } := by
  rcases applyFnTClosure_ok_of_mem_mapM
      ctx st1 st2 p p1 argEtyp argPoison argPred bodyState fuel tcls results
      (FnTClosure.regular x body tenv) hmap hmem with
    ⟨first, _hfirst_mem, happly⟩
  rcases applyFnTClosure_regular_structure
      ctx st1 st2 p p1 argEtyp argPoison argPred bodyState fuel x body tenv first happly with
    ⟨fuelBody, hfuel⟩
  have happly_succ :
      applyFnTClosure .ioFree (FnTClosure.regular x body tenv) st1 st2 p p1
        argEtyp argPoison argPred ctx bodyState (Nat.succ fuelBody) = .ok first := by
    simpa [hfuel] using happly
  rcases applyFnTClosure_regular_inv
      ctx st1 st2 p p1 argEtyp argPoison argPred bodyState fuelBody x body tenv first happly_succ with
    ⟨result3, htc_body, hsub, hfirst_eq⟩
  exact ⟨fuelBody, first, result3, happly, hfuel, htc_body, hsub, hfirst_eq⟩

-- Forall₂ gives an existence for membership on the right.
lemma list_Forall2_exists_of_mem_right
    {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β} :
    List.Forall₂ R xs ys →
    ∀ y ∈ ys, ∃ x, x ∈ xs ∧ R x y := by
  intro h
  induction h with
  | nil =>
      intro y hy
      cases hy
  | cons hxy _htail ih =>
      intro y hymem
      simp [List.mem_cons] at hymem
      cases hymem with
      | inl hyeq =>
          subst hyeq
          exact ⟨_, by simp, hxy⟩
      | inr hyrest =>
          rcases ih y hyrest with ⟨x, hxmem, hR⟩
          exact ⟨x, by simp [hxmem], hR⟩

-- If `List.mapM f xs` succeeds and `y ∈ ys`, then some `x ∈ xs` maps to `y`.
lemma list_mapM_ok_mem_output_exists_input
  {α β ε : Type}
  (f : α → Except ε β)
  {xs : List α} {ys : List β} {y : β}
  (hmap : List.mapM f xs = .ok ys)
  (hmem : y ∈ ys) :
  ∃ x, x ∈ xs ∧ f x = .ok y := by
  have hforall2 :
      List.Forall₂ (fun x y => f x = Except.ok y) xs ys :=
    List.mapM_Except_ok_implies_forall2 xs f ys hmap
  rcases list_Forall2_exists_of_mem_right (R := fun x y => f x = Except.ok y) hforall2 y hmem with
    ⟨x, hxmem, hxy⟩
  exact ⟨x, hxmem, hxy⟩

-- Body typecheck in app context: wfTypeResult for result3 from typecheckExpr_preserves_wfTypeResult.
lemma applyFnTClosure_regular_body_wfTypeResult
  (ctx : TypeContext) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuelBody : Nat)
  (x : Name) (body : Expr) (tenv : CapturedVarEnv)
  (hwf1 : wfTypeResult result1)
  (ctx'' : TypeContext)
  (hctx'' : ctx'' = { ctx with
      pc := joinPoison p (joinPoison p1 ctx.pc)
      memEnv := result1.memEnv'
      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
        ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
      tagEnv := result1.tagEnv'
      nextTag := result1.nextTag'
      nextLoc := result1.nextLoc'
      regime := result1.regime' })
  (result3 : TypeResult)
  (htc : typecheckExpr .ioFree ctx'' body fuelBody = .ok result3) :
  wfTypeResult result3 := by
  have hwf_ctx'' : wfTypeContext ctx'' := by
    rw [hctx'']
    simp only [wfTypeContext]
    exact hwf1
  exact typecheckExpr_preserves_wfTypeResult ctx'' body fuelBody result3 hwf_ctx''
    (by simpa [typecheck] using htc)

-- Helper lemmas for wfTagMeaningCtx in closure body contexts.
-- These need to be before applyFnTClosure_ok_wfTypeResult.

lemma QTypRespectsTagMeaning_of_arrow_captured_lookup
  (tm : TagMeaning)
  (qtRes : QTyp) (st1 st2 : Typ) (p : Poison) (tcls : List FnTClosure)
  (xFun y : Name) (body : Expr) (σcap : CapturedVarEnv) (qtCap : QTyp)
  (hresTm : QTypRespectsTagMeaning tm qtRes)
  (hetyp : qtRes.etyp = ETyp.arrow st1 st2 p tcls)
  (hmem : FnTClosure.regular xFun body σcap ∈ tcls)
  (hlookup : σcap.lookup y = some qtCap) :
  QTypRespectsTagMeaning tm qtCap := by
  intro qt k d hinq hqd
  have hcapMem : (y, qtCap) ∈ σcap :=
    List_lookup_some_mem y qtCap σcap (by simpa [CapturedVarEnv.lookup_eq] using hlookup)
  have hroot :
      QTypInQTyp qtCap qtRes :=
    QTypInQTyp.in_arrow qtCap qtRes st1 st2 p tcls
      (FnTClosure.regular xFun body σcap) y
      hetyp hmem (by simpa [fnCapturedEnv] using hcapMem)
  exact hresTm (QTypInQTyp.trans qt qtCap qtRes hinq hroot) hqd

lemma wfTagMeaningCtx_ofCaptured_from_arrow
  (tm : TagMeaning) (ctxMem : TypeContext)
  (qtRes : QTyp) (st1 st2 : Typ) (p : Poison) (tcls : List FnTClosure)
  (xFun : Name) (body : Expr) (σcap : CapturedVarEnv)
  (hctxTm : wfTagMeaningCtx tm ctxMem)
  (hresTm : QTypRespectsTagMeaning tm qtRes)
  (hetyp : qtRes.etyp = ETyp.arrow st1 st2 p tcls)
  (hmem : FnTClosure.regular xFun body σcap ∈ tcls) :
  wfTagMeaningCtx tm { ctxMem with varEnv := VarTypeEnv.ofCaptured σcap } := by
  unfold wfTagMeaningCtx at hctxTm ⊢
  refine EnvRespectsTagMeaning.intro ?_
  intro k d hgd
  rcases hgd with ⟨qt, k, d, hinq, hm⟩
  cases hinq with
  | inVar _ _ y _qt qtRoot hlookup hinqRoot =>
      have hlookupCap : σcap.lookup y = some qtRoot :=
        list_lookup_of_ofCaptured_lookup σcap y qtRoot (by simpa using hlookup)
      have hrootTm : QTypRespectsTagMeaning tm qtRoot :=
        QTypRespectsTagMeaning_of_arrow_captured_lookup
          tm qtRes st1 st2 p tcls xFun y body σcap qtRoot
          hresTm hetyp hmem hlookupCap
      exact hrootTm hinqRoot hm
  | inMem _ _ l _qt qtRoot hlookup hinqRoot =>
      exact hctxTm.1 (GuardDescInEnvsDeep.intro qt k d
        (QTypInEnvs.inMem ctxMem.varEnv ctxMem.memEnv l qt qtRoot hlookup hinqRoot) hm)

lemma wfTagMeaningCtx_closure_body
  (tm : TagMeaning) (ctx : TypeContext) (result1 : TypeResult)
  (qtRes : QTyp) (st1 st2 : Typ) (p : Poison) (tcls : List FnTClosure)
  (xFun : Name) (body : Expr) (σcap : CapturedVarEnv)
  (xArg : Name) (argQt : QTyp)
  (hctxTm : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm : QTypRespectsTagMeaning tm qtRes)
  (hetyp : qtRes.etyp = ETyp.arrow st1 st2 p tcls)
  (hmem : FnTClosure.regular xFun body σcap ∈ tcls)
  (hargTm : QTypRespectsTagMeaning tm argQt) :
  wfTagMeaningCtx tm
    { ctx with
      memEnv := result1.memEnv'
      tagEnv := result1.tagEnv'
      nextLoc := result1.nextLoc'
      nextTag := result1.nextTag'
      regime := result1.regime'
      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) xArg argQt } := by
  let ctxCap : TypeContext :=
    { ctx with
      memEnv := result1.memEnv'
      tagEnv := result1.tagEnv'
      nextLoc := result1.nextLoc'
      nextTag := result1.nextTag'
      regime := result1.regime'
      varEnv := VarTypeEnv.ofCaptured σcap }
  have hctxCapTm : wfTagMeaningCtx tm ctxCap := by
    have hcapTm :
        wfTagMeaningCtx tm { (ctxAfter ctx result1) with varEnv := VarTypeEnv.ofCaptured σcap } :=
      wfTagMeaningCtx_ofCaptured_from_arrow
        tm (ctxAfter ctx result1) qtRes st1 st2 p tcls xFun body σcap
        hctxTm hresTm hetyp hmem
    simpa [ctxCap, ctxAfter] using hcapTm
  have hbodyTm :
      wfTagMeaningCtx tm { ctxCap with varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) xArg argQt } :=
    wfTagMeaningCtx_varEnv_ext tm ctxCap xArg argQt hctxCapTm hargTm
  simpa [ctxCap] using hbodyTm

lemma PExpr_toExpr_of_toPExpr?_some : ∀ (e : Expr) (pe : PExpr),
    Expr.toPExpr? e = some pe → PExpr.toExpr pe = e
  | .unit, _, h => by simp [Expr.toPExpr?] at h; subst h; rfl
  | .num n, _, h => by simp [Expr.toPExpr?] at h; subst h; rfl
  | .bool b, _, h => by simp [Expr.toPExpr?] at h; subst h; rfl
  | .str s, _, h => by simp [Expr.toPExpr?] at h; subst h; rfl
  | .var x, _, h => by simp [Expr.toPExpr?] at h; subst h; rfl
  | .op e1 o e2, pe, h => by
      simp only [Expr.toPExpr?] at h
      cases h1 : Expr.toPExpr? e1 with
      | none => simp [h1] at h
      | some pe1 =>
        cases h2 : Expr.toPExpr? e2 with
        | none => simp [h1, h2] at h
        | some pe2 =>
          simp [h1, h2] at h
          subst h; simp [PExpr.toExpr]
          exact ⟨PExpr_toExpr_of_toPExpr?_some e1 pe1 h1, PExpr_toExpr_of_toPExpr?_some e2 pe2 h2⟩
  | .unaryop o e1, pe, h => by
      simp only [Expr.toPExpr?] at h
      cases h1 : Expr.toPExpr? e1 with
      | none => simp [h1] at h
      | some pe1 =>
        simp [h1] at h; subst h; simp [PExpr.toExpr]
        exact PExpr_toExpr_of_toPExpr?_some e1 pe1 h1
  | .ite e1 e2 e3, pe, h => by
      simp only [Expr.toPExpr?] at h
      cases h1 : Expr.toPExpr? e1 with
      | none => simp [h1] at h
      | some pe1 =>
        cases h2 : Expr.toPExpr? e2 with
        | none => simp [h1, h2] at h
        | some pe2 =>
          cases h3 : Expr.toPExpr? e3 with
          | none => simp [h1, h2, h3] at h
          | some pe3 =>
            simp [h1, h2, h3] at h; subst h; simp [PExpr.toExpr]
            exact ⟨PExpr_toExpr_of_toPExpr?_some e1 pe1 h1,
                   PExpr_toExpr_of_toPExpr?_some e2 pe2 h2,
                   PExpr_toExpr_of_toPExpr?_some e3 pe3 h3⟩
  | .deref e1, pe, h => by
      simp only [Expr.toPExpr?] at h
      cases h1 : Expr.toPExpr? e1 with
      | none => simp [h1] at h
      | some pe1 =>
        simp [h1] at h; subst h; simp [PExpr.toExpr]
        exact PExpr_toExpr_of_toPExpr?_some e1 pe1 h1
  | .vlet x e1 e2, pe, h => by
      simp only [Expr.toPExpr?] at h
      cases h1 : Expr.toPExpr? e1 with
      | none => simp [h1] at h
      | some pe1 =>
        cases h2 : Expr.toPExpr? e2 with
        | none => simp [h1, h2] at h
        | some pe2 =>
          simp [h1, h2] at h; subst h; simp [PExpr.toExpr]
          exact ⟨PExpr_toExpr_of_toPExpr?_some e1 pe1 h1, PExpr_toExpr_of_toPExpr?_some e2 pe2 h2⟩
  | .app e1 e2, pe, h => by
      simp only [Expr.toPExpr?] at h
      cases h1 : Expr.toPExpr? e1 with
      | none => simp [h1] at h
      | some pe1 =>
        cases h2 : Expr.toPExpr? e2 with
        | none => simp [h1, h2] at h
        | some pe2 =>
          simp [h1, h2] at h; subst h; simp [PExpr.toExpr]
          exact ⟨PExpr_toExpr_of_toPExpr?_some e1 pe1 h1, PExpr_toExpr_of_toPExpr?_some e2 pe2 h2⟩
  | .newRef _, _, h => by simp [Expr.toPExpr?] at h
  | .assign _ _, _, h => by simp [Expr.toPExpr?] at h
  | .seq _ _, _, h => by simp [Expr.toPExpr?] at h
  | .kwhile _ _, _, h => by simp [Expr.toPExpr?] at h
  | .fn _ _ _ _, _, h => by simp [Expr.toPExpr?] at h
  | .pfn _ _ _ _, _, h => by simp [Expr.toPExpr?] at h
  | .rand _, _, h => by simp [Expr.toPExpr?] at h
  | .frand _, _, h => by simp [Expr.toPExpr?] at h
  | .printString _, _, h => by simp [Expr.toPExpr?] at h
  | .printInt _, _, h => by simp [Expr.toPExpr?] at h
  | .externVal _ _ _, _, h => by simp [Expr.toPExpr?] at h
  | .externFn _ _ _ _, _, h => by simp [Expr.toPExpr?] at h
  | .externPfn _ _ _, _, h => by simp [Expr.toPExpr?] at h

lemma QTypRespectsTagMeaning_of_parrow_captured_lookup
  (tm : TagMeaning)
  (qtRes : QTyp) (st1 st2 : Typ) (p : Poison) (tcls : List PFnTClosure)
  (xFun y : Name) (pbody : PExpr) (σcap : CapturedVarEnv) (qtCap : QTyp)
  (hresTm : QTypRespectsTagMeaning tm qtRes)
  (hetyp : qtRes.etyp = ETyp.parrow st1 st2 p tcls)
  (hmem : PFnTClosure.regular xFun pbody σcap ∈ tcls)
  (hlookup : σcap.lookup y = some qtCap) :
  QTypRespectsTagMeaning tm qtCap := by
  intro qt k d hinq hqd
  have hcapMem : (y, qtCap) ∈ σcap :=
    List_lookup_some_mem y qtCap σcap (by simpa [CapturedVarEnv.lookup_eq] using hlookup)
  have hroot :
      QTypInQTyp qtCap qtRes :=
    QTypInQTyp.in_parrow qtCap qtRes st1 st2 p tcls
      (PFnTClosure.regular xFun pbody σcap) y
      hetyp hmem (by simpa [pfnCapturedEnv] using hcapMem)
  exact hresTm (QTypInQTyp.trans qt qtCap qtRes hinq hroot) hqd

lemma wfTagMeaningCtx_ofCaptured_from_parrow
  (tm : TagMeaning) (ctxMem : TypeContext)
  (qtRes : QTyp) (st1 st2 : Typ) (p : Poison) (tcls : List PFnTClosure)
  (xFun : Name) (pbody : PExpr) (σcap : CapturedVarEnv)
  (hctxTm : wfTagMeaningCtx tm ctxMem)
  (hresTm : QTypRespectsTagMeaning tm qtRes)
  (hetyp : qtRes.etyp = ETyp.parrow st1 st2 p tcls)
  (hmem : PFnTClosure.regular xFun pbody σcap ∈ tcls) :
  wfTagMeaningCtx tm { ctxMem with varEnv := VarTypeEnv.ofCaptured σcap } := by
  unfold wfTagMeaningCtx at hctxTm ⊢
  refine EnvRespectsTagMeaning.intro ?_
  intro k d hgd
  rcases hgd with ⟨qt, k, d, hinq, hm⟩
  cases hinq with
  | inVar _ _ y _qt qtRoot hlookup hinqRoot =>
      have hlookupCap : σcap.lookup y = some qtRoot :=
        list_lookup_of_ofCaptured_lookup σcap y qtRoot (by simpa using hlookup)
      have hrootTm : QTypRespectsTagMeaning tm qtRoot :=
        QTypRespectsTagMeaning_of_parrow_captured_lookup
          tm qtRes st1 st2 p tcls xFun y pbody σcap qtRoot
          hresTm hetyp hmem hlookupCap
      exact hrootTm hinqRoot hm
  | inMem _ _ l _qt qtRoot hlookup hinqRoot =>
      exact hctxTm.1 (GuardDescInEnvsDeep.intro qt k d
        (QTypInEnvs.inMem ctxMem.varEnv ctxMem.memEnv l qt qtRoot hlookup hinqRoot) hm)

lemma wfTagMeaningCtx_pclosure_body
  (tm : TagMeaning) (ctx : TypeContext) (result1 : TypeResult)
  (qtRes : QTyp) (st1 st2 : Typ) (p : Poison) (tcls : List PFnTClosure)
  (xFun : Name) (pbody : PExpr) (σcap : CapturedVarEnv)
  (xArg : Name) (argQt : QTyp)
  (hctxTm : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm : QTypRespectsTagMeaning tm qtRes)
  (hetyp : qtRes.etyp = ETyp.parrow st1 st2 p tcls)
  (hmem : PFnTClosure.regular xFun pbody σcap ∈ tcls)
  (hargTm : QTypRespectsTagMeaning tm argQt) :
  wfTagMeaningCtx tm
    { ctx with
      memEnv := result1.memEnv'
      tagEnv := result1.tagEnv'
      nextLoc := result1.nextLoc'
      nextTag := result1.nextTag'
      regime := result1.regime'
      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) xArg argQt } := by
  let ctxCap : TypeContext :=
    { ctx with
      memEnv := result1.memEnv'
      tagEnv := result1.tagEnv'
      nextLoc := result1.nextLoc'
      nextTag := result1.nextTag'
      regime := result1.regime'
      varEnv := VarTypeEnv.ofCaptured σcap }
  have hctxCapTm : wfTagMeaningCtx tm ctxCap := by
    have hcapTm :
        wfTagMeaningCtx tm { (ctxAfter ctx result1) with varEnv := VarTypeEnv.ofCaptured σcap } :=
      wfTagMeaningCtx_ofCaptured_from_parrow
        tm (ctxAfter ctx result1) qtRes st1 st2 p tcls xFun pbody σcap
        hctxTm hresTm hetyp hmem
    simpa [ctxCap, ctxAfter] using hcapTm
  have hbodyTm :
      wfTagMeaningCtx tm { ctxCap with varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) xArg argQt } :=
    wfTagMeaningCtx_varEnv_ext tm ctxCap xArg argQt hctxCapTm hargTm
  simpa [ctxCap] using hbodyTm

-- Layer A (per-member): static facts for successful closure-application typing.
-- wfTypeResult for the body result comes from stepFR IH (StepFR for body → wfTypeResult).
-- These are intentionally isolated so `stepFR_app` can consume them now and we
-- can prove them incrementally.
lemma applyFnTClosure_ok_wfTypeResult
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (hwf1 : wfTypeResult result1)
  (tcl : FnTClosure)
  (r : TypeResult)
  (happly :
    applyFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel = .ok r) :
  wfTypeResult r := by
  cases fuel with
  | zero =>
    unfold applyFnTClosure at happly
    simp at happly
  | succ fuelBody =>
    cases tcl with
    | regular x body tenv =>
      rcases applyFnTClosure_regular_inv ctx st1 st2 p p1 argEtyp argPoison argPred result1 fuelBody
          x body tenv r (by simpa using happly) with
        ⟨result3, htc_body, _hsub, hfirst⟩
      have hwf3 := applyFnTClosure_regular_body_wfTypeResult ctx p p1 argEtyp argPoison argPred
        result1 fuelBody x body tenv hwf1
        { ctx with
          pc := joinPoison p (joinPoison p1 ctx.pc)
          memEnv := result1.memEnv'
          varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
            ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
          tagEnv := result1.tagEnv'
          nextTag := result1.nextTag'
          nextLoc := result1.nextLoc'
          regime := result1.regime' }
        rfl result3 htc_body
      rw [hfirst]
      exact hwf3
    | extern x retSpec effects capturedEnv =>
      exfalso
      exact applyFnTClosure_ioFree_extern_fails ctx st1 st2 p p1 argEtyp argPoison argPred result1
        (Nat.succ fuelBody) x retSpec effects capturedEnv r happly

-- ==========================================================================
-- typecheckExpr preserves regimeConsistentWithCtx
-- ==========================================================================
-- This is a key preservation theorem: successful typechecking in ioFree mode
-- preserves the regime consistency invariant (tagEnv/regime agreement + bound).

-- Helper: regimeConsistentWithCtx only depends on tagEnv, regime, nextTag
lemma regimeConsistentWithCtx_of_tagEnv_regime_nextTag
    (ctx₁ ctx₂ : TypeContext)
    (htag : ctx₂.tagEnv = ctx₁.tagEnv)
    (hreg : ctx₂.regime = ctx₁.regime)
    (hnt : ctx₂.nextTag = ctx₁.nextTag)
    (h : regimeConsistentWithCtx ctx₁) :
    regimeConsistentWithCtx ctx₂ := by
  simp only [regimeConsistentWithCtx] at h ⊢
  rw [htag, hreg, hnt]; exact h

lemma joinTypeResults_tagEnvConsistentWithRegime'
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (h_join : joinTypeResults ctx first rest = .ok res)
  (h_first : regimeConsistentWithCtx (ctxAfter ctx first))
  (h_rest : ∀ r ∈ rest, regimeConsistentWithCtx (ctxAfter ctx r)) :
  tagEnvConsistentWithRegime (ctxAfter ctx res).tagEnv (ctxAfter ctx res).regime := by
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
        TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvsStrong acc.2.1 result.memEnv',
              joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred,
              joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 result.regime',
              max acc.2.2.2.2.2.2.1 result.nextLoc',
              max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_tag :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        tagEnvConsistentWithRegime acc.2.2.2.2.1 acc.2.2.2.2.2.1 →
        (∀ r ∈ rs', regimeConsistentWithCtx (ctxAfter ctx r)) →
        tagEnvConsistentWithRegime acc'.2.2.2.2.1 acc'.2.2.2.2.2.1 := by
    intro rs' acc acc' hfold hacc hrs
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        cases hfold
        exact hacc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv',
                joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred,
                joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc',
                max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have hx :
                regimeConsistentWithCtx (ctxAfter ctx x) :=
              hrs x (by simp)
            have hx_tag : tagEnvConsistentWithRegime x.tagEnv' x.regime' := by
              simpa [regimeConsistentWithCtx, ctxAfter] using hx.1
            have hacc1 :
                tagEnvConsistentWithRegime acc1.2.2.2.2.1 acc1.2.2.2.2.2.1 := by
              simpa [acc1] using
                (tagEnvConsistentWithRegime_join
                  acc.2.2.2.2.1 x.tagEnv' acc.2.2.2.2.2.1 x.regime'
                  hacc hx_tag)
            have hrs_tail :
                ∀ r ∈ xs, regimeConsistentWithCtx (ctxAfter ctx r) := by
              intro r hr
              exact hrs r (by simp [hr])
            exact ih (acc := acc1) hfold_tail hacc1 hrs_tail
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at h_join
      cases hcheck :
          (List.foldlM
            (fun x result =>
              match result.qualType with
              | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                if beqETypSignature etyp resEtyp = false then
                  Except.error
                    (toString "Closure alternatives produced incompatible result types: " ++
                      toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
                else Except.ok ())
            () rest : Except String Unit) with
      | error err =>
          erw [hcheck] at h_join
          simp at h_join
      | ok _ =>
          erw [hcheck] at h_join
          simp at h_join
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                  first.nextLoc', first.nextTag') rest with
          | error err =>
              erw [hfold] at h_join
              simp at h_join
          | ok a =>
              erw [hfold] at h_join
              simp at h_join
              subst res
              have h_first_tag :
                  tagEnvConsistentWithRegime first.tagEnv' first.regime' := by
                simpa [regimeConsistentWithCtx, ctxAfter] using h_first.1
              exact
                h_fold_tag rest
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                    first.nextLoc', first.nextTag')
                  a hfold h_first_tag h_rest

lemma joinTypeResults_regimeConsistentWithCtx
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (h_join : joinTypeResults ctx first rest = .ok res)
  (h_first : regimeConsistentWithCtx (ctxAfter ctx first))
  (h_rest : ∀ r ∈ rest, regimeConsistentWithCtx (ctxAfter ctx r)) :
  regimeConsistentWithCtx (ctxAfter ctx res) := by
  constructor
  · exact joinTypeResults_tagEnvConsistentWithRegime' ctx first rest res h_join h_first h_rest
  · -- res.regime'.bound ≤ res.nextTag'
    -- From joinTypeResults_regime_bound_le_head: res.regime'.bound ≤ first.regime'.bound
    -- From h_first: first.regime'.bound ≤ first.nextTag'
    -- From joinTypeResults_nextTag_eq_max: res.nextTag' = List.max (first.nextTag' :: ...)
    -- So first.nextTag' ≤ res.nextTag'
    have hbound_le_first := joinTypeResults_regime_bound_le_head ctx first rest res h_join
    have hfirst_bound : first.regime'.bound ≤ first.nextTag' := by
      simpa [regimeConsistentWithCtx, ctxAfter] using h_first.2
    have h_nextTag_eq := joinTypeResults_nextTag_eq_max ctx first rest res h_join
    have hfirst_le_res : first.nextTag' ≤ res.nextTag' := by
      rw [h_nextTag_eq]
      apply List.le_max_of_mem
      simp
    show (ctxAfter ctx res).regime.bound ≤ (ctxAfter ctx res).nextTag
    simp [ctxAfter]
    exact Nat.le_trans (Nat.le_trans hbound_le_first hfirst_bound) hfirst_le_res

lemma typecheckExpr_preserves_regimeConsistentWithCtx_main :
    ∀ (fuel : Nat) (ctx : TypeContext) (e : Expr) (res : TypeResult),
    regimeConsistentWithCtx ctx →
    typecheck .ioFree ctx e fuel = .ok res →
    regimeConsistentWithCtx (ctxAfter ctx res) := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
    intro ctx e res hreg htc
    have IH' : ∀ m < fuel, ∀ (ctx' : TypeContext) (e' : Expr) (res' : TypeResult),
        regimeConsistentWithCtx ctx' →
        typecheck .ioFree ctx' e' m = .ok res' →
        regimeConsistentWithCtx (ctxAfter ctx' res') := by
      intro m hm ctx' e' res'; exact IH m hm ctx' e' res'
    unfold typecheck at htc
    cases fuel with
    | zero =>
        unfold typecheckExpr at htc; simp at htc
    | succ fuel' =>
        unfold typecheckExpr at htc
        have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
        cases e with
        -- Literals and simple forms: tagEnv'/regime'/nextTag' = ctx fields
        | num _n =>
            unfold typecheckInt at htc; simp [pure, Except.pure] at htc; cases htc
            simpa [ctxAfter, regimeConsistentWithCtx]
        | bool _b =>
            unfold typecheckBool at htc; simp [pure, Except.pure] at htc; cases htc
            simpa [ctxAfter, regimeConsistentWithCtx]
        | unit =>
            unfold typecheckUnit at htc; simp [pure, Except.pure] at htc; cases htc
            simpa [ctxAfter, regimeConsistentWithCtx]
        | str _s =>
            unfold typecheckString at htc; simp [pure, Except.pure] at htc; cases htc
            simpa [ctxAfter, regimeConsistentWithCtx]
        | var x =>
            -- typecheckVar always returns tagEnv' = ctx.tagEnv, regime' = ctx.regime, nextTag' = ctx.nextTag
            simp at htc
            unfold typecheckVar at htc
            simp only [bind, Except.bind] at htc
            cases hlookup : ctx.varEnv.lookup x with
            | none => simp [hlookup] at htc
            | some qt =>
              simp [hlookup] at htc
              cases qt with
              | mk etyp poison pred =>
                simp at htc
                cases pred with
                | noPred =>
                  simp [pure, Except.pure] at htc; cases htc
                  simpa [ctxAfter, regimeConsistentWithCtx]
                | guardOnly k =>
                  simp at htc
                  by_cases hfn : etyp.isFunctionType
                  · simp [hfn] at htc
                  · simp [hfn] at htc
                    revert htc; generalize ctx.tagEnv[k]? = tv
                    cases tv with
                    | none => intro htc; simp at htc; cases htc; simpa [ctxAfter, regimeConsistentWithCtx]
                    | some tv => cases tv with | mk val deps =>
                      cases val <;> intro htc <;> simp at htc <;> cases htc <;>
                        simpa [ctxAfter, regimeConsistentWithCtx]
                | guardClosure k tcls ptcls body_t =>
                  simp at htc
                  by_cases hfn : etyp.isFunctionType
                  · simp [hfn] at htc
                  · simp [hfn] at htc
                    revert htc; generalize ctx.tagEnv[k]? = tv
                    cases tv with
                    | none => intro htc; simp at htc; cases htc; simpa [ctxAfter, regimeConsistentWithCtx]
                    | some tv => cases tv with | mk val deps =>
                      cases val <;> intro htc <;> simp at htc <;> cases htc <;>
                        simpa [ctxAfter, regimeConsistentWithCtx]
        | fn _ _ _ _ =>
            unfold typecheckFn at htc; simp [pure, Except.pure] at htc; cases htc
            simpa [ctxAfter, regimeConsistentWithCtx]
        | pfn x st1 body st2 =>
            unfold typecheckPfn at htc
            simp [bind, Except.bind] at htc
            cases h_topexpr : body.toPExpr with
            | error _ => simp [h_topexpr] at htc
            | ok _ =>
              simp [h_topexpr, pure, Except.pure] at htc; subst htc
              simpa [ctxAfter, regimeConsistentWithCtx]
        -- Impossible in ioFree mode
        | externVal _ _ _ =>
            exfalso; simp at htc; unfold typecheckExternVal at htc
            have heq : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
            simp only [heq, ite_true, bind, Except.bind] at htc
            exact absurd htc (Except.error_ne_ok _ _)
        | externFn _ _ _ _ =>
            exfalso; simp at htc; unfold typecheckExternFn at htc
            have heq : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
            simp only [heq, ite_true, bind, Except.bind] at htc
            exact absurd htc (Except.error_ne_ok _ _)
        | externPfn _ _ _ =>
            exfalso; simp at htc; unfold typecheckExternPfn at htc
            have heq : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
            simp only [heq, ite_true, bind, Except.bind] at htc
            exact absurd htc (Except.error_ne_ok _ _)
        | rand _ =>
            simp at htc
            exact absurd htc (typecheckRand_ioFree_impossible ctx _ fuel' res)
        | frand _ =>
            simp at htc
            exact absurd htc (typecheckFrand_ioFree_impossible ctx _ fuel' res)
        | printInt _ =>
            simp at htc
            exact absurd htc (typecheckPrintInt_ioFree_impossible ctx _ fuel' res)
        | printString _ =>
            simp at htc
            exact absurd htc (typecheckPrintString_ioFree_impossible ctx _ fuel' res)
        -- Compound expressions with sub-expression chaining
        | unaryop op e1 =>
            have hstruct := typecheckUnaryOp_structure ctx op e1 fuel' res htc
            rcases hstruct with ⟨result1, _, htc1, _, _, htag, _, hnextTag, hreg', _, _, _⟩
            have htc1' : typecheck .ioFree ctx e1 (fuel' - 1) = .ok result1 := by simpa using htc1
            have hIH := IH' (fuel' - 1) (by omega) ctx e1 result1 hreg htc1'
            simp only [ctxAfter, regimeConsistentWithCtx] at hIH ⊢
            rwa [htag, hnextTag, hreg']
        | deref e1 =>
            have hstruct := typecheckDeref_structure ctx e1 fuel' res htc
            rcases hstruct with ⟨result1, htc1, _, htag, _, hnextTag, hreg'⟩
            have htc1' : typecheck .ioFree ctx e1 (fuel' - 1) = .ok result1 := by simpa using htc1
            have hIH := IH' (fuel' - 1) (by omega) ctx e1 result1 hreg htc1'
            simp only [ctxAfter, regimeConsistentWithCtx] at hIH ⊢
            rwa [htag, hnextTag, hreg']
        | newRef e1 =>
            have hstruct := typecheckNewRef_structure ctx e1 fuel' res htc
            rcases hstruct with ⟨result1, _, htc1, _, _, _, _, _, _, htag, _, hnextTag, hreg'⟩
            have htc1' : typecheck .ioFree ctx e1 (fuel' - 1) = .ok result1 := by simpa using htc1
            have hIH := IH' (fuel' - 1) (by omega) ctx e1 result1 hreg htc1'
            simp only [ctxAfter, regimeConsistentWithCtx] at hIH ⊢
            rwa [htag, hnextTag, hreg']
        | op e1 op e2 =>
            have hstruct := typecheckOp_structure ctx e1 e2 op fuel' res htc
            rcases hstruct with ⟨result1, result2, _, htc1, htc2, _, _, htag, _, hnextTag, hregime', _, _, _⟩
            have htc1' : typecheck .ioFree ctx e1 (fuel' - 1) = .ok result1 := by simpa using htc1
            have hIH1 := IH' (fuel' - 1) (by omega) ctx e1 result1 hreg htc1'
            have hreg_mid : regimeConsistentWithCtx (updateCtxFromResult ctx result1) := by
              apply regimeConsistentWithCtx_of_tagEnv_regime_nextTag (ctxAfter ctx result1)
              · simp [ctxAfter, updateCtxFromResult]
              · simp [ctxAfter, updateCtxFromResult]
              · simp [ctxAfter, updateCtxFromResult]
              · exact hIH1
            have htc2' : typecheck .ioFree (updateCtxFromResult ctx result1) e2 (fuel' - 1) = .ok result2 := by simpa using htc2
            have hIH2 := IH' (fuel' - 1) (by omega) (updateCtxFromResult ctx result1) e2 result2 hreg_mid htc2'
            simp only [ctxAfter, regimeConsistentWithCtx] at hIH2 ⊢
            rwa [htag, hnextTag, hregime']
        | seq e1 e2 =>
            have hstruct := typecheckSeq_structure ctx e1 e2 fuel' res htc
            rcases hstruct with ⟨result1, ctx', htc1, hctx', htc2⟩
            have htc1' : typecheck .ioFree ctx e1 (fuel' - 1) = .ok result1 := by simpa using htc1
            have hIH1 := IH' (fuel' - 1) (by omega) ctx e1 result1 hreg htc1'
            have hreg_mid : regimeConsistentWithCtx ctx' := by
              rw [hctx']
              apply regimeConsistentWithCtx_of_tagEnv_regime_nextTag (ctxAfter ctx result1)
              · simp [ctxAfter, updateCtxFromResult]
              · simp [ctxAfter, updateCtxFromResult]
              · simp [ctxAfter, updateCtxFromResult]
              · exact hIH1
            have htc2' : typecheck .ioFree ctx' e2 (fuel' - 1) = .ok res := by simpa using htc2
            exact IH' (fuel' - 1) (by omega) ctx' e2 res hreg_mid htc2'
        | vlet x e1 e2 =>
            have hstruct := typecheckVlet_structure ctx x e1 e2 fuel' res htc
            rcases hstruct with ⟨result1, result2, ctx', htc1, hctx', htc2, _, _, htag, _, hnextTag, hregime', _, _⟩
            have htc1' : typecheck .ioFree ctx e1 (fuel' - 1) = .ok result1 := by simpa using htc1
            have hIH1 := IH' (fuel' - 1) (by omega) ctx e1 result1 hreg htc1'
            have hreg_mid : regimeConsistentWithCtx ctx' := by
              rw [hctx']
              apply regimeConsistentWithCtx_of_tagEnv_regime_nextTag (ctxAfter ctx result1)
              · simp [ctxAfter]
              · simp [ctxAfter]
              · simp [ctxAfter]
              · exact hIH1
            have htc2' : typecheck .ioFree ctx' e2 (fuel' - 1) = .ok result2 := by simpa using htc2
            have hIH2 := IH' (fuel' - 1) (by omega) ctx' e2 result2 hreg_mid htc2'
            simp only [ctxAfter, regimeConsistentWithCtx] at hIH2 ⊢
            rwa [htag, hnextTag, hregime']
        | assign e1 e2 =>
            unfold typecheckAssign at htc
            cases fuel' with
            | zero => simp at htc
            | succ fuel'' =>
            simp only [bind, Except.bind] at htc
            cases h_tc1 : typecheckExpr .ioFree ctx e1 fuel'' with
            | error _ => simp [h_tc1] at htc
            | ok result1 =>
              simp only [h_tc1] at htc
              have htc1' : typecheck .ioFree ctx e1 fuel'' = .ok result1 := by simpa using h_tc1
              have hIH1 := IH' fuel'' (by omega) ctx e1 result1 hreg htc1'
              cases h_qt1 : result1.qualType with
              | mk etyp1 p1 pred1 =>
                rw [h_qt1] at htc; simp at htc
                cases etyp1 with
                | ref ls =>
                  simp at htc
                  set ctx2 : TypeContext := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }
                  have hreg2 : regimeConsistentWithCtx ctx2 := by
                    apply regimeConsistentWithCtx_of_tagEnv_regime_nextTag (ctxAfter ctx result1)
                    · simp [ctxAfter, ctx2]
                    · simp [ctxAfter, ctx2]
                    · simp [ctxAfter, ctx2]
                    · exact hIH1
                  cases h_tc2 : typecheckExpr .ioFree ctx2 e2 fuel'' with
                  | error _ => simp [h_tc2] at htc
                  | ok result2 =>
                    simp only [h_tc2] at htc
                    have htc2' : typecheck .ioFree ctx2 e2 fuel'' = .ok result2 := by simpa using h_tc2
                    have hIH2 := IH' fuel'' (by omega) ctx2 e2 result2 hreg2 htc2'
                    cases h_qt2 : result2.qualType with
                    | mk etyp2 p2 pred2 =>
                      rw [h_qt2] at htc; simp at htc
                      by_cases h_etyp2_int : etyp2 = ETyp.int
                      · subst h_etyp2_int; simp at htc; cases htc
                        simp only [ctxAfter, regimeConsistentWithCtx] at hIH2 ⊢
                        constructor
                        · exact invalidateRegimeDeps_preserves_true result2.tagEnv' result2.regime' ls hIH2.1
                        · simpa [invalidateRegimeDeps] using hIH2.2
                      · simp [h_etyp2_int] at htc
                | _ => simp at htc
        | ite e1 e2 e3 =>
            -- typecheckExpr dispatches to typecheckIf with fuel already decremented to fuel'
            have hstruct := typecheckIf_structure ctx e1 e2 e3 fuel' res htc
            rcases hstruct with h1 | h2 | h3 | h4
            · -- Mode 1: R(k) = true, then-branch effective
              rcases h1 with ⟨k, deps, _, hRk, _, _, _, res2, htc2, hmem, htag, _, hnextTag, hregEq, _⟩
              have hreg_true : regimeConsistentWithCtx { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ } := by
                constructor
                · exact tagEnvConsistentWithRegime_insert_true ctx.tagEnv ctx.regime k deps hreg.1 hRk
                · exact hreg.2
              -- htc2 is at fuel' - 1; convert to typecheck call for IH
              have htc2' : typecheck .ioFree { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ } e2 (fuel' - 1) = .ok res2 := by simpa using htc2
              have hIH2 := IH' (fuel' - 1) (by omega) { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ } e2 res2 hreg_true htc2'
              simp only [ctxAfter, regimeConsistentWithCtx] at hIH2 ⊢
              rwa [htag, hnextTag, hregEq]
            · -- Mode 2: R(k) = false, else-branch effective
              rcases h2 with ⟨k, deps, _, _, _, _, _, res3, htc3, hmem, htag, _, hnextTag, hregEq, _⟩
              have hreg_false : regimeConsistentWithCtx { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩ } := by
                constructor
                · exact tagEnvConsistentWithRegime_insert_false ctx.tagEnv ctx.regime k deps hreg.1
                · exact hreg.2
              have htc3' : typecheck .ioFree { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩ } e3 (fuel' - 1) = .ok res3 := by simpa using htc3
              have hIH3 := IH' (fuel' - 1) (by omega) { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩ } e3 res3 hreg_false htc3'
              simp only [ctxAfter, regimeConsistentWithCtx] at hIH3 ⊢
              rwa [htag, hnextTag, hregEq]
            · -- Mode 3: R(k) = none, conservative join
              -- Tag insertion k↦true breaks tagEnvConsistentWithRegime when R(k)=none
              -- This case requires specialized handling (parallel to stepFR_ite_mode3 sorry)
              sorry
            · -- Mode 4: Standard (matchGuard fails), join of both branches
              rcases h4 with ⟨_, res1, htc1, _, res2, htc2, res3, htc3, hmem, htag, _, hnextTag, hregEq, _⟩
              have htc1' : typecheck .ioFree ctx e1 (fuel' - 1) = .ok res1 := by simpa using htc1
              have hIH1 := IH' (fuel' - 1) (by omega) ctx e1 res1 hreg htc1'
              -- Build ctx' (after e1)
              set ctx' := { ctx with memEnv := res1.memEnv', tagEnv := res1.tagEnv',
                                     nextLoc := res1.nextLoc', nextTag := res1.nextTag', regime := res1.regime' }
              have hreg1 : regimeConsistentWithCtx ctx' := by
                apply regimeConsistentWithCtx_of_tagEnv_regime_nextTag (ctxAfter ctx res1)
                · simp [ctxAfter, ctx']
                · simp [ctxAfter, ctx']
                · simp [ctxAfter, ctx']
                · exact hIH1
              -- ctx'' just changes pc, doesn't affect regimeConsistentWithCtx
              set ctx'' := { ctx' with pc := joinPoison ctx.pc res1.qualType.poison }
              have hreg1' : regimeConsistentWithCtx ctx'' := hreg1
              have htc2' : typecheck .ioFree ctx'' e2 (fuel' - 1) = .ok res2 := by simpa using htc2
              have hIH2 := IH' (fuel' - 1) (by omega) ctx'' e2 res2 hreg1' htc2'
              -- ctxForE3: same tagEnv/regime as ctx'', but nextLoc/nextTag from res2
              set ctxForE3 := { ctx'' with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
              -- ctxForE3 has tagEnv/regime from ctx'' (= res1's), but nextLoc/nextTag from res2
              -- Need: tagEnvConsistentWithRegime ctx''.tagEnv ctx''.regime (from IH1)
              -- Need: ctx''.regime.bound ≤ res2.nextTag' (from IH1 bound + nextTag mono)
              have hIH1_tagEnv : tagEnvConsistentWithRegime res1.tagEnv' res1.regime' := by
                have h := hIH1; simp only [ctxAfter, regimeConsistentWithCtx] at h; exact h.1
              have hIH1_bound : res1.regime'.bound ≤ res1.nextTag' := by
                have h := hIH1; simp only [ctxAfter, regimeConsistentWithCtx] at h; exact h.2
              have hnextTag_mono : res1.nextTag' ≤ res2.nextTag' := by
                have : ctx''.nextTag ≤ res2.nextTag' :=
                  typecheck_nextTag_mono .ioFree ctx'' e2 (fuel' - 1) res2 htc2'
                simpa [ctx'', ctx'] using this
              have hreg2 : regimeConsistentWithCtx ctxForE3 := by
                constructor
                · -- tagEnvConsistentWithRegime: ctxForE3.tagEnv = ctx''.tagEnv = res1.tagEnv'
                  show tagEnvConsistentWithRegime ctxForE3.tagEnv ctxForE3.regime
                  simp only [ctxForE3, ctx'', ctx']
                  exact hIH1_tagEnv
                · -- bound: ctxForE3.regime.bound = res1.regime'.bound ≤ res1.nextTag' ≤ res2.nextTag'
                  show ctxForE3.regime.bound ≤ ctxForE3.nextTag
                  simp only [ctxForE3, ctx'', ctx']
                  exact Nat.le_trans hIH1_bound hnextTag_mono
              have htc3' : typecheck .ioFree ctxForE3 e3 (fuel' - 1) = .ok res3 := by simpa using htc3
              have hIH3 := IH' (fuel' - 1) (by omega) ctxForE3 e3 res3 hreg2 htc3'
              have hIH2' : regimeConsistentWithCtx (ctxAfter ctx'' res2) := hIH2
              simp only [ctxAfter, regimeConsistentWithCtx] at hIH2' hIH3 ⊢
              rw [htag, hnextTag, hregEq]
              constructor
              · exact tagEnvConsistentWithRegime_join res2.tagEnv' res3.tagEnv' res2.regime' res3.regime' hIH2'.1 hIH3.1
              · -- (joinRegimes res2.regime' res3.regime').bound ≤ max res2.nextTag' res3.nextTag'
                show (joinRegimes res2.regime' res3.regime').bound ≤ max res2.nextTag' res3.nextTag'
                unfold joinRegimes; simp only
                exact Nat.le_trans (Nat.min_le_left _ _) (Nat.le_trans hIH2'.2 (Nat.le_max_left _ _))
        | app e1 e2 =>
            simp at htc
            -- htc : typecheckApp .ioFree ctx e1 e2 fuel' = .ok res
            cases fuel' with
            | zero => simp [typecheckApp] at htc
            | succ fuel'' =>
            -- htc : typecheckApp .ioFree ctx e1 e2 (fuel''.succ) = .ok res
            rcases typecheckApp_arrow_structure_full ctx e1 e2 fuel'' res htc with
              ⟨result2, result1, etyp2, p2, pred2, _hqt2, htc2, htc1, hcases⟩
            -- IH on e2 (fuel'' < fuel''.succ.succ = fuel)
            have hIH2 := IH' fuel'' (by omega) ctx e2 result2 hreg htc2
            -- Build regime consistency for the e1 typecheck context
            have hreg' : regimeConsistentWithCtx
                (⟨ctx.pc, result2.regime', result2.memEnv', ctx.varEnv, result2.tagEnv',
                  result2.nextLoc', result2.nextTag', ctx.pureCtx⟩ : TypeContext) := by
              apply regimeConsistentWithCtx_of_tagEnv_regime_nextTag (ctxAfter ctx result2)
              · simp [ctxAfter]
              · simp [ctxAfter]
              · simp [ctxAfter]
              · exact hIH2
            -- IH on e1 (fuel'' < fuel)
            have hIH1 := IH' fuel'' (by omega) _ e1 result1 hreg' htc1
            -- Helper: for any closure result r from applyFnTClosure, regimeConsistentWithCtx (ctxAfter ctx r)
            -- Derive regimeConsistentWithCtx for the body context (same tagEnv/regime/nextTag as ctxAfter _ result1)
            have hIH1_tagEnv : tagEnvConsistentWithRegime result1.tagEnv' result1.regime' := by
              have := hIH1.1; simp [ctxAfter] at this; exact this
            have hIH1_bound : result1.regime'.bound ≤ result1.nextTag' := by
              have := hIH1.2; simp [ctxAfter] at this; exact this
            have h_fn_closure_reg :
                ∀ (st1 st2 : Typ) (p p1 : Poison) (tcls : List FnTClosure)
                  (results : List TypeResult),
                  List.mapM (fun tcl => applyFnTClosure .ioFree tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel'') tcls = .ok results →
                  ∀ r, r ∈ results → regimeConsistentWithCtx (ctxAfter ctx r) := by
              intro st1 st2 p p1 tcls results hmap r hr
              rcases list_mapM_ok_mem_output_exists_input
                  (f := fun tcl => applyFnTClosure .ioFree tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel'')
                  (hmap := hmap) (hmem := hr) with
                ⟨tcl, _htcl_mem, happly⟩
              cases tcl with
              | regular x body env =>
                cases fuel'' with
                | zero => simp [applyFnTClosure] at happly
                | succ k =>
                  simp only [applyFnTClosure, bind, Except.bind] at happly
                  split at happly
                  · exact absurd happly (Except.error_ne_ok _ _)
                  · next result3 htcBody =>
                    cases hqt3 : result3.qualType with
                    | mk etyp3 p3 pred3 =>
                    simp only [hqt3] at happly
                    split at happly
                    · simp at happly
                    · next _hsub =>
                      simp only [pure, Except.pure] at happly
                      cases happly
                      have hreg_body : regimeConsistentWithCtx
                          { ctx with
                            pc := joinPoison p (joinPoison p1 ctx.pc),
                            memEnv := result1.memEnv',
                            varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x ⟨etyp2, joinPoison ctx.pc p2, pred2⟩,
                            tagEnv := result1.tagEnv', nextTag := result1.nextTag',
                            nextLoc := result1.nextLoc', regime := result1.regime' } := by
                        exact ⟨hIH1_tagEnv, hIH1_bound⟩
                      have htcBody' : typecheck .ioFree
                          { ctx with
                            pc := joinPoison p (joinPoison p1 ctx.pc),
                            memEnv := result1.memEnv',
                            varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x ⟨etyp2, joinPoison ctx.pc p2, pred2⟩,
                            tagEnv := result1.tagEnv', nextTag := result1.nextTag',
                            nextLoc := result1.nextLoc', regime := result1.regime' }
                          body k = .ok result3 := by simpa using htcBody
                      have hIH_body := IH' k (by omega) _ body result3 hreg_body htcBody'
                      simp only [ctxAfter, regimeConsistentWithCtx] at hIH_body ⊢
                      exact hIH_body
              | extern x retSpec effects capturedEnv =>
                cases fuel'' with
                | zero => simp [applyFnTClosure] at happly
                | succ k =>
                  simp only [applyFnTClosure] at happly
                  have hioFree : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
                  rw [hioFree] at happly
                  simp only [ite_true] at happly; simp only [bind, Except.bind] at happly
                  exact absurd happly (by simp)
            -- Helper: for any closure result r from applyPFnTClosure, regimeConsistentWithCtx (ctxAfter ctx r)
            have h_pfn_closure_reg :
                ∀ (st1 st2 : Typ) (p p1 : Poison) (tcls : List PFnTClosure)
                  (results : List TypeResult),
                  List.mapM (fun tcl => applyPFnTClosure .ioFree tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel'') tcls = .ok results →
                  ∀ r, r ∈ results → regimeConsistentWithCtx (ctxAfter ctx r) := by
              intro st1 st2 p p1 tcls results hmap r hr
              rcases list_mapM_ok_mem_output_exists_input
                  (f := fun tcl => applyPFnTClosure .ioFree tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel'')
                  (hmap := hmap) (hmem := hr) with
                ⟨tcl, _htcl_mem, happly⟩
              cases tcl with
              | regular x body env =>
                cases fuel'' with
                | zero => simp [applyPFnTClosure] at happly
                | succ k =>
                  simp only [applyPFnTClosure, bind, Except.bind] at happly
                  split at happly
                  · exact absurd happly (Except.error_ne_ok _ _)
                  · next result3 htcBody =>
                    cases hqt3 : result3.qualType with
                    | mk etyp3 p3 pred3 =>
                    simp only [hqt3] at happly
                    split at happly
                    · simp at happly
                    · next _hsub =>
                      simp only [pure, Except.pure] at happly
                      cases happly
                      set bodyCtx := { ctx with
                          pc := joinPoison p (joinPoison ctx.pc p1),
                          memEnv := result1.memEnv',
                          varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x ⟨etyp2, joinPoison ctx.pc p2, pred2⟩,
                          tagEnv := result1.tagEnv', nextTag := result1.nextTag',
                          pureCtx := true,
                          nextLoc := result1.nextLoc', regime := result1.regime' }
                      have hreg_body : regimeConsistentWithCtx bodyCtx := by
                        constructor
                        · exact hIH1.1
                        · exact hIH1.2
                      have htcBody' : typecheck .ioFree bodyCtx (PExpr.toExpr body) k = .ok result3 := by simpa using htcBody
                      have hIH_body := IH' k (by omega) bodyCtx (PExpr.toExpr body) result3 hreg_body htcBody'
                      apply regimeConsistentWithCtx_of_tagEnv_regime_nextTag (ctxAfter bodyCtx result3)
                      · simp [ctxAfter]
                      · simp [ctxAfter]
                      · simp [ctxAfter]
                      · exact hIH_body
              | extern x retSpec capturedEnv =>
                cases fuel'' with
                | zero => simp [applyPFnTClosure] at happly
                | succ k =>
                  simp only [applyPFnTClosure] at happly
                  have hioFree : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
                  rw [hioFree] at happly
                  simp only [ite_true] at happly; simp only [bind, Except.bind] at happly
                  exact absurd happly (by simp)
            -- Now handle arrow/parrow cases
            rcases hcases with
              ⟨st1, st2, p, p1, tcls, results, first, rest, _hetyp1, _hp1, _hpure, _hne, _hsub, hmap, hresults, h_join⟩ |
              ⟨st1, st2, p, p1, tcls, results, first, rest, _hetyp1, _hp1, _hne, _hsub, hmap, hresults, h_join⟩
            · -- Arrow case
              subst hresults
              have h_all_reg : ∀ r, r ∈ (first :: rest) → regimeConsistentWithCtx (ctxAfter ctx r) :=
                h_fn_closure_reg st1 st2 p p1 tcls (first :: rest) hmap
              exact joinTypeResults_regimeConsistentWithCtx ctx first rest res h_join
                (h_all_reg first (List.mem_cons_self ..))
                (fun r hr => h_all_reg r (List.mem_cons_of_mem _ hr))
            · -- Parrow case
              subst hresults
              have h_all_reg : ∀ r, r ∈ (first :: rest) → regimeConsistentWithCtx (ctxAfter ctx r) :=
                h_pfn_closure_reg st1 st2 p p1 tcls (first :: rest) hmap
              exact joinTypeResults_regimeConsistentWithCtx ctx first rest res h_join
                (h_all_reg first (List.mem_cons_self ..))
                (fun r hr => h_all_reg r (List.mem_cons_of_mem _ hr))
        | kwhile e1 e2 =>
            simp at htc
            sorry -- permanently postponed: kwhile proofs are out of active scope

lemma typecheckExpr_preserves_regimeConsistentWithCtx
    (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (hreg : regimeConsistentWithCtx ctx)
    (htc : typecheck .ioFree ctx e fuel = .ok res) :
    regimeConsistentWithCtx (ctxAfter ctx res) :=
  typecheckExpr_preserves_regimeConsistentWithCtx_main fuel ctx e res hreg htc

/-- Mix lemma: combine inVar evidence from one (σ, Γ₁) pair with inMem evidence from
    another (σ₂, Γ) pair. Works because `QTypInEnvs.inVar` only uses σ and
    `QTypInEnvs.inMem` only uses Γ. -/
lemma EnvRespectsTagMeaning_mix
    (tm : TagMeaning) (σ₁ : VarTypeEnv) (Γ₁ : MemoryTypeEnv) (σ₂ : VarTypeEnv) (Γ₂ : MemoryTypeEnv)
    (h1 : EnvRespectsTagMeaning tm σ₁ Γ₁)
    (h2 : EnvRespectsTagMeaning tm σ₂ Γ₂) :
    EnvRespectsTagMeaning tm σ₁ Γ₂ := by
  refine EnvRespectsTagMeaning.intro ?_
  intro k d hgd
  rcases hgd with ⟨qt, k, d, hinenvs, hguard⟩
  cases hinenvs with
  | inVar _ _ x _ qtRoot hlookup hinq =>
    -- Same σ₁ lookup, swap Γ₂ for Γ₁
    exact h1.1 (GuardDescInEnvsDeep.intro qt k d
      (QTypInEnvs.inVar σ₁ Γ₁ x qt qtRoot hlookup hinq) hguard)
  | inMem _ _ l _ qtRoot hlookup hinq =>
    -- Same Γ₂ lookup, swap σ₁ for σ₂
    exact h2.1 (GuardDescInEnvsDeep.intro qt k d
      (QTypInEnvs.inMem σ₂ Γ₂ l qt qtRoot hlookup hinq) hguard)

/-- typecheckIf always produces a result with pred = noPred in ioFree mode. -/
lemma typecheckIf_pred_noPred
    (ctx : TypeContext) (e1 e2 e3 : Expr) (fuel : Nat) (res : TypeResult)
    (htc : typecheckIf .ioFree ctx e1 e2 e3 fuel = .ok res) :
    res.qualType.pred = Predicate.noPred := by
  cases fuel with
  | zero => simp [typecheckIf] at htc
  | succ fuel' =>
    unfold typecheckIf at htc
    simp only [bind, Except.bind] at htc
    cases hmatch : matchGuard e1 ctx.memEnv ctx.varEnv fuel' with
    | ok kd =>
      obtain ⟨k, deps⟩ := kd
      simp only [hmatch] at htc
      cases hregime : ctx.regime.lookup? k with
      | some b =>
        cases b with
        | true =>
          simp only [hregime] at htc
          cases htc1 : typecheckExpr .ioFree { ctx with pureCtx := true } e1 fuel' with
          | error e => simp only [htc1] at htc; cases htc
          | ok result1 =>
            simp only [htc1] at htc
            match hq1 : result1.qualType with
            | ⟨etyp1, _, _⟩ =>
              simp only [hq1] at htc
              by_cases hbool : etyp1 = ETyp.bool
              · have heq_mode : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
                simp only [hbool, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
                  pure, Except.pure, heq_mode] at htc
                cases htc2 : typecheckExpr .ioFree _ e2 fuel' with
                | error e => rw [htc2] at htc; simp at htc
                | ok result2 =>
                  rw [htc2] at htc; simp at htc
                  match hq2 : result2.qualType with
                  | ⟨_, _, _⟩ =>
                    simp only [hq2] at htc
                    injection htc with heq_res; rw [← heq_res]
              · simp only [hbool, bne_iff_ne, ne_eq] at htc
                cases htc
        | false =>
          simp only [hregime] at htc
          cases htc1 : typecheckExpr .ioFree { ctx with pureCtx := true } e1 fuel' with
          | error e => simp only [htc1] at htc; cases htc
          | ok result1 =>
            simp only [htc1] at htc
            match hq1 : result1.qualType with
            | ⟨etyp1, _, _⟩ =>
              simp only [hq1] at htc
              by_cases hbool : etyp1 = ETyp.bool
              · have heq_mode : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
                simp only [hbool, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
                  pure, Except.pure, heq_mode] at htc
                cases htc3 : typecheckExpr .ioFree _ e3 fuel' with
                | error e => rw [htc3] at htc; simp at htc
                | ok result3 =>
                  rw [htc3] at htc; simp at htc
                  match hq3 : result3.qualType with
                  | ⟨_, _, _⟩ =>
                    simp only [hq3] at htc
                    injection htc with heq_res; rw [← heq_res]
              · simp only [hbool, bne_iff_ne, ne_eq] at htc
                cases htc
      | none =>
        simp only [hregime] at htc
        cases htc1 : typecheckExpr .ioFree { ctx with pureCtx := true } e1 fuel' with
        | error e => simp only [htc1] at htc; cases htc
        | ok result1 =>
          simp only [htc1] at htc
          match hq1 : result1.qualType with
          | ⟨etyp1, _, _⟩ =>
            simp only [hq1] at htc
            by_cases hbool : etyp1 = ETyp.bool
            · simp only [hbool, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
                pure, Except.pure] at htc
              cases htc2 : typecheckExpr .ioFree _ e2 fuel' with
              | error e => rw [htc2] at htc; simp at htc
              | ok result2 =>
                rw [htc2] at htc; simp at htc
                match hq2 : result2.qualType with
                | ⟨etyp2, _, _⟩ =>
                  simp only [hq2] at htc
                  cases htc3 : typecheckExpr .ioFree _ e3 fuel' with
                  | error e => rw [htc3] at htc; cases htc
                  | ok result3 =>
                    rw [htc3] at htc
                    match hq3 : result3.qualType with
                    | ⟨etyp3, _, _⟩ =>
                      simp only [hq3] at htc
                      by_cases hcompat : beqETypSignature etyp2 etyp3 = false
                      · simp only [hcompat, ↓reduceIte] at htc; cases htc
                      · have hcompat' : beqETypSignature etyp2 etyp3 = true := by
                          cases h : beqETypSignature etyp2 etyp3 <;> simp_all
                        simp only [hcompat'] at htc; cases htc; simp [*]
            · simp only [hbool, bne_iff_ne, ne_eq] at htc
              cases htc
    | error err =>
      simp only [hmatch] at htc
      cases htc1 : typecheckExpr .ioFree ctx e1 fuel' with
      | error e => simp only [htc1] at htc; cases htc
      | ok result1 =>
        simp only [htc1] at htc
        match hq1 : result1.qualType with
        | ⟨etyp1, _, _⟩ =>
          simp only [hq1] at htc
          by_cases hbool : etyp1 = ETyp.bool
          · simp only [hbool, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at htc
            cases htc2 : typecheckExpr .ioFree _ e2 fuel' with
            | error e => rw [htc2] at htc; cases htc
            | ok result2 =>
              rw [htc2] at htc
              match hq2 : result2.qualType with
              | ⟨etyp2, _, _⟩ =>
                simp only [hq2] at htc
                cases htc3 : typecheckExpr .ioFree _ e3 fuel' with
                | error e => rw [htc3] at htc; cases htc
                | ok result3 =>
                  rw [htc3] at htc
                  match hq3 : result3.qualType with
                  | ⟨etyp3, _, _⟩ =>
                    simp only [hq3] at htc
                    by_cases hcompat : beqETypSignature etyp2 etyp3 = false
                    · simp only [hcompat, Bool.not_eq_true', ↓reduceIte] at htc; cases htc
                    · have hcompat' : beqETypSignature etyp2 etyp3 = true := by
                        cases h : beqETypSignature etyp2 etyp3 <;> simp_all
                      simp only [hcompat', Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                        pure, Except.pure, Except.ok.injEq] at htc
                      subst htc; rfl
          · simp only [hbool, bne_iff_ne, ne_eq] at htc
            cases htc

/-- Transport QTypRespectsTagMeaning across same etyp when pred becomes noPred.
    The self-descriptor vanishes (noPred → none), and nested descriptors through etyp
    are unchanged. -/
lemma QTypRespectsTagMeaning_of_etyp_noPred
    (tm : TagMeaning) (qt qt' : QTyp)
    (h : QTypRespectsTagMeaning tm qt)
    (hetyp : qt'.etyp = qt.etyp)
    (hpred : qt'.pred = Predicate.noPred) :
    QTypRespectsTagMeaning tm qt' := by
  intro q k d hinq hqd
  have htr := QTypInQTyp_transport_etyp hinq hetyp
  cases htr with
  | inl hEq =>
    subst hEq
    simp [qtypGuardDesc?, hpred] at hqd
  | inr hinq' =>
    exact h hinq' hqd

lemma EnvRespectsTagMeaning_joinMemEnvsStrong'
    (tm : TagMeaning) (σ : VarTypeEnv) (Γ1 Γ2 : MemoryTypeEnv)
    (h1 : EnvRespectsTagMeaning tm σ Γ1) :
    EnvRespectsTagMeaning tm σ (joinMemEnvsStrong Γ1 Γ2) := by
  refine EnvRespectsTagMeaning.intro ?_
  intro k d hgd
  rcases hgd with ⟨qt, k, d, hinq, hdesc⟩
  cases hinq with
  | inVar _ _ x _ qtRoot hlookup hsub =>
      exact h1.1 (GuardDescInEnvsDeep.intro qt k d (QTypInEnvs.inVar σ Γ1 x qt qtRoot hlookup hsub) hdesc)
  | inMem _ _ l qt0 qtRoot hlookup hsub =>
      have hcontains : (joinMemEnvsStrong Γ1 Γ2).contains l := by
        have hlookup_eq : (joinMemEnvsStrong Γ1 Γ2).lookup l = some qtRoot := by
          rw [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?]
          exact hlookup
        exact memEnv_contains_of_lookup_some (joinMemEnvsStrong Γ1 Γ2) l qtRoot hlookup_eq
      have hor := joinMemEnvsStrong_contains_implies_or Γ1 Γ2 l hcontains
      cases hor with
      | inl hleft =>
          by_cases h2none : Γ2.lookup l = none
          · have h2none_get : Γ2[l]? = none := by
              simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using h2none
            have hleft_eq :=
              joinMemEnvsStrong_lookup_eq_left_of_right_none Γ1 Γ2 l hleft h2none_get
            cases h1lookup : Γ1.lookup l with
            | none =>
                rw [h1lookup, hlookup] at hleft_eq
                simp at hleft_eq
            | some qt1 =>
                rw [h1lookup] at hleft_eq
                rw [hlookup] at hleft_eq
                have hroot_eq : qtRoot = ⟨qt1.etyp, qt1.poison, Predicate.noPred⟩ := by
                  simpa using hleft_eq
                have htm_qt1 : QTypRespectsTagMeaning tm qt1 :=
                  EnvRespectsTagMeaning_mem_lookup_qtyp tm σ Γ1 l qt1 h1 h1lookup
                have htm_root : QTypRespectsTagMeaning tm qtRoot := by
                  apply QTypRespectsTagMeaning_transport_etyp_noGuard tm qt1 qtRoot htm_qt1
                  · simpa using congrArg QTyp.etyp hroot_eq
                  · simp [hroot_eq, qtypGuardDesc?]
                exact htm_root hsub hdesc
          · have h2some : Γ2[l]? ≠ none := by
              intro hnone
              exact h2none (by simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hnone)
            have h1some : Γ1[l]? ≠ none := by
              intro hnone
              have hnot_some : ¬Option.isSome (Γ1[l]?) := by simp [hnone]
              have hmem : l ∈ Γ1 := (Std.ExtTreeMap.contains_iff_mem).mp hleft
              exact hnot_some ((Std.ExtTreeMap.mem_iff_isSome_getElem?).mp hmem)
            rcases Option.ne_none_iff_exists'.1 h1some with ⟨e1, h1some'⟩
            rcases Option.ne_none_iff_exists'.1 h2some with ⟨e2, h2some'⟩
            let qt1 : QTyp := ⟨ETyp.int, e1.poison, e1.pred⟩
            let qt2 : QTyp := ⟨ETyp.int, e2.poison, e2.pred⟩
            have h1lookup' : Γ1.lookup l = some qt1 := by
              simp only [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?, h1some', qt1, Option.map]
            have h2lookup' : Γ2.lookup l = some qt2 := by
              simp only [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?, h2some', qt2, Option.map]
            have hlookupW : (joinMemEnvs Γ1 Γ2).lookup l = some qtRoot := by
              rw [← joinMemEnvsStrong_lookup_eq_joinMemEnvs_of_both_lookup Γ1 Γ2 l qt1 qt2 h1lookup' h2lookup']
              exact hlookup
            exact (QTypRespectsTagMeaning_joinMem_lookup tm σ Γ1 Γ2 l qtRoot h1 hlookupW h1some h2some) hsub hdesc
      | inr hright =>
          by_cases h1none : Γ1.lookup l = none
          · have h1none_get : Γ1[l]? = none := by
              simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using h1none
            have hright_eq :=
              joinMemEnvsStrong_lookup_eq_right_of_left_none Γ1 Γ2 l h1none_get hright
            cases h2lookup : Γ2.lookup l with
            | none =>
                rw [h2lookup, hlookup] at hright_eq
                simp at hright_eq
            | some qt2 =>
                rw [h2lookup] at hright_eq
                rw [hlookup] at hright_eq
                have hroot_eq : qtRoot = ⟨qt2.etyp, qt2.poison, Predicate.noPred⟩ := by
                  simpa using hright_eq
                have hqt2_int : qt2.etyp = ETyp.int :=
                  memEnv_lookup_etyp_int Γ2 l qt2 h2lookup
                have hnotfun : qtRoot.etyp.isFunctionType = false := by
                  simp [hroot_eq, hqt2_int, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                have hself : qt = qtRoot := QTypInQTyp_eq_of_nonFunctionTarget hsub hnotfun
                subst hself
                simp [hroot_eq, qtypGuardDesc?] at hdesc
          · have h1some : Γ1[l]? ≠ none := by
              intro hnone
              exact h1none (by simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hnone)
            have h2some : Γ2[l]? ≠ none := by
              intro hnone
              have hnot_some : ¬Option.isSome (Γ2[l]?) := by simp [hnone]
              have hmem : l ∈ Γ2 := (Std.ExtTreeMap.contains_iff_mem).mp hright
              exact hnot_some ((Std.ExtTreeMap.mem_iff_isSome_getElem?).mp hmem)
            rcases Option.ne_none_iff_exists'.1 h1some with ⟨e1, h1some'⟩
            rcases Option.ne_none_iff_exists'.1 h2some with ⟨e2, h2some'⟩
            let qt1 : QTyp := ⟨ETyp.int, e1.poison, e1.pred⟩
            let qt2 : QTyp := ⟨ETyp.int, e2.poison, e2.pred⟩
            have h1lookup' : Γ1.lookup l = some qt1 := by
              simp only [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?, h1some', qt1, Option.map]
            have h2lookup' : Γ2.lookup l = some qt2 := by
              simp only [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?, h2some', qt2, Option.map]
            have hlookupW : (joinMemEnvs Γ1 Γ2).lookup l = some qtRoot := by
              rw [← joinMemEnvsStrong_lookup_eq_joinMemEnvs_of_both_lookup Γ1 Γ2 l qt1 qt2 h1lookup' h2lookup']
              exact hlookup
            exact (QTypRespectsTagMeaning_joinMem_lookup tm σ Γ1 Γ2 l qtRoot h1 hlookupW h1some h2some) hsub hdesc

-- A single join-step for QTypRespectsTagMeaning: joining two tag-meaning-respecting
-- qualified types produces another tag-meaning-respecting qualified type.
-- (Moved before _main because ite modes 3/4 need it.)
lemma QTypRespectsTagMeaning_joinStep
    (tm : TagMeaning) (e1 e2 : ETyp) (p1 p2 : Poison) (pred1 pred2 : Predicate)
    (h1 : QTypRespectsTagMeaning tm ⟨e1, p1, pred1⟩)
    (h2 : QTypRespectsTagMeaning tm ⟨e2, p2, pred2⟩) :
    QTypRespectsTagMeaning tm ⟨joinETyps e1 e2 p1 p2, joinPoison p1 p2, joinPredicates pred1 pred2⟩ := by
  intro qt' k d hinq hqd
  have hdecomp :
      QTypInQTyp qt' ⟨e1, p1, pred1⟩ ∨
      QTypInQTyp qt' ⟨e2, p2, pred2⟩ ∨
      qt' = ⟨joinETyps e1 e2 p1 p2, joinPoison p1 p2, joinPredicates pred1 pred2⟩ :=
    (QTypInQTyp.recOn
        (motive := fun qt' qt₂ _ =>
          qt₂ = ⟨joinETyps e1 e2 p1 p2, joinPoison p1 p2, joinPredicates pred1 pred2⟩ →
          QTypInQTyp qt' ⟨e1, p1, pred1⟩ ∨ QTypInQTyp qt' ⟨e2, p2, pred2⟩ ∨
          qt' = ⟨joinETyps e1 e2 p1 p2, joinPoison p1 p2, joinPredicates pred1 pred2⟩)
        hinq
        (fun _ hn => Or.inr (Or.inr hn))
        (fun qtInner qtOuter st₁ st₂ _p tcls tcl x hetyp htcl hcap hjoined => by
          subst hjoined
          cases e1 with
          | arrow st1a st2a pa1 tcls1 =>
              cases e2 with
              | arrow st1b st2b pb1 tcls2 =>
                  simp only [joinETyps] at hetyp
                  by_cases hshape : st1a == st1b && st2a == st2b
                  · simp only [hshape, ↓reduceIte] at hetyp
                    obtain ⟨rfl, rfl, _, rfl⟩ := ETyp.arrow.inj hetyp
                    cases mem_mergeFnTClosures_inv tcls1 tcls2 tcl htcl with
                    | inl h =>
                        exact Or.inl (QTypInQTyp.in_arrow qtInner ⟨ETyp.arrow st1a st2a pa1 tcls1, p1, pred1⟩
                          st1a st2a pa1 tcls1 tcl x rfl h hcap)
                    | inr h =>
                        exact Or.inr (Or.inl (QTypInQTyp.in_arrow qtInner ⟨ETyp.arrow st1b st2b pb1 tcls2, p2, pred2⟩
                          st1b st2b pb1 tcls2 tcl x rfl h hcap))
                  · simp only [hshape, Bool.false_eq_true, ↓reduceIte] at hetyp
                    obtain ⟨rfl, rfl, _, rfl⟩ := ETyp.arrow.inj hetyp
                    exact Or.inl (QTypInQTyp.in_arrow qtInner ⟨ETyp.arrow st1a st2a pa1 tcls1, p1, pred1⟩
                      st1a st2a pa1 tcls1 tcl x rfl htcl hcap)
              | _ =>
                  simp only [joinETyps] at hetyp
                  obtain ⟨rfl, rfl, _, rfl⟩ := ETyp.arrow.inj hetyp
                  exact Or.inl (QTypInQTyp.in_arrow qtInner ⟨ETyp.arrow st1a st2a pa1 tcls1, p1, pred1⟩
                    st1a st2a pa1 tcls1 tcl x rfl htcl hcap)
          | int | bool | unit | string => simp [joinETyps] at hetyp
          | ref ls =>
              cases e2 with
              | ref ls2 =>
                  simp [joinETyps] at hetyp
              | _ => simp [joinETyps] at hetyp
          | parrow st1a st2a pa1 ptcls1 =>
              cases e2 with
              | parrow st1b st2b pb1 ptcls2 =>
                  simp only [joinETyps] at hetyp
                  split_ifs at hetyp
              | _ => simp [joinETyps] at hetyp)
        (fun qtInner qtOuter st₁ st₂ _p tcls tcl x hetyp htcl hcap hjoined => by
          subst hjoined
          cases e1 with
          | parrow st1a st2a pa1 ptcls1 =>
              cases e2 with
              | parrow st1b st2b pb1 ptcls2 =>
                  simp only [joinETyps] at hetyp
                  by_cases hshape : st1a == st1b && st2a == st2b
                  · simp only [hshape, ↓reduceIte] at hetyp
                    obtain ⟨rfl, rfl, _, rfl⟩ := ETyp.parrow.inj hetyp
                    cases mem_mergePFnTClosures_inv ptcls1 ptcls2 tcl htcl with
                    | inl h =>
                        exact Or.inl (QTypInQTyp.in_parrow qtInner ⟨ETyp.parrow st1a st2a pa1 ptcls1, p1, pred1⟩
                          st1a st2a pa1 ptcls1 tcl x rfl h hcap)
                    | inr h =>
                        exact Or.inr (Or.inl (QTypInQTyp.in_parrow qtInner ⟨ETyp.parrow st1b st2b pb1 ptcls2, p2, pred2⟩
                          st1b st2b pb1 ptcls2 tcl x rfl h hcap))
                  · simp only [hshape, Bool.false_eq_true, ↓reduceIte] at hetyp
                    obtain ⟨rfl, rfl, _, rfl⟩ := ETyp.parrow.inj hetyp
                    exact Or.inl (QTypInQTyp.in_parrow qtInner ⟨ETyp.parrow st1a st2a pa1 ptcls1, p1, pred1⟩
                      st1a st2a pa1 ptcls1 tcl x rfl htcl hcap)
              | _ =>
                  simp only [joinETyps] at hetyp
                  obtain ⟨rfl, rfl, _, rfl⟩ := ETyp.parrow.inj hetyp
                  exact Or.inl (QTypInQTyp.in_parrow qtInner ⟨ETyp.parrow st1a st2a pa1 ptcls1, p1, pred1⟩
                    st1a st2a pa1 ptcls1 tcl x rfl htcl hcap)
          | int | bool | unit | string => simp [joinETyps] at hetyp
          | ref ls =>
              cases e2 with
              | ref ls2 =>
                  simp [joinETyps] at hetyp
              | _ => simp [joinETyps] at hetyp
          | arrow st1a st2a pa1 tcls1 =>
              cases e2 with
              | arrow st1b st2b pb1 tcls2 =>
                  simp only [joinETyps] at hetyp
                  split_ifs at hetyp
              | _ => simp [joinETyps] at hetyp)
        (fun a b _c h₁₂ _h₂₃ ih₁₂ ih₂₃ hjoined =>
          (ih₂₃ hjoined).elim
            (fun h_e1 => Or.inl (QTypInQTyp.trans a b _ h₁₂ h_e1))
            (fun h => h.elim
              (fun h_e2 => Or.inr (Or.inl (QTypInQTyp.trans a b _ h₁₂ h_e2)))
              (fun heq => ih₁₂ heq)))) rfl
  rcases hdecomp with (h_e1 | h_e2 | h_self)
  · exact h1 h_e1 hqd
  · exact h2 h_e2 hqd
  · subst h_self
    have hpj := qtypGuardDesc?_eq_some_pred_guardClosure hqd
    have hp1 := (joinPredicates_eq_guardClosure hpj).1
    exact h1 (QTypInQTyp.self _) (by simp [qtypGuardDesc?, hp1])

lemma applyFnTClosure_ok_wfTagMeaningCtx_byIH
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (tcls : List FnTClosure)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (bodyIH :
    ∀ (fuel' : Nat), fuel' < fuel →
      ∀ (ctx : TypeContext) (e : Expr) (res : TypeResult),
      wfTagMeaningCtx tm ctx →
      typecheck .ioFree ctx e fuel' = .ok res →
      wfTagMeaningCtx tm (ctxAfter ctx res))
  (tcl : FnTClosure) (r : TypeResult)
  (hctxTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm1 : QTypRespectsTagMeaning tm result1.qualType)
  (hetyp1 : result1.qualType.etyp = ETyp.arrow st1 st2 p tcls)
  (hmem_tcl : tcl ∈ tcls)
  (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, argPoison, argPred⟩)
  (happly :
    applyFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel = .ok r) :
  wfTagMeaningCtx tm (ctxAfter ctx r) := by
  cases tcl with
  | regular x body env =>
    cases fuel with
    | zero => simp [applyFnTClosure] at happly
    | succ fuel' =>
      simp only [applyFnTClosure, bind, Except.bind] at happly
      split at happly
      · exact absurd happly (Except.error_ne_ok _ _)
      · next result3 htcBody =>
        cases hqt3 : result3.qualType with
        | mk etyp3 p3 pred3 =>
        simp only [hqt3] at happly
        split at happly
        · simp at happly
        · next hsub =>
          simp only [pure, Except.pure] at happly
          cases happly
          set bodyCtx := { ctx with
              pc := joinPoison p (joinPoison p1 ctx.pc),
              memEnv := result1.memEnv',
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩,
              tagEnv := result1.tagEnv', nextTag := result1.nextTag',
              nextLoc := result1.nextLoc', regime := result1.regime' }
          have htcBody' : typecheck .ioFree bodyCtx body fuel' = .ok result3 := by
            simpa [typecheck] using htcBody
          have hargTm' : QTypRespectsTagMeaning tm ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩ :=
            QTypRespectsTagMeaning_transport_etyp_pred tm
              ⟨argEtyp, argPoison, argPred⟩ ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
              hargTm rfl rfl
          have hwf_body : wfTagMeaningCtx tm bodyCtx := by
            simpa [bodyCtx, ctxAfter] using
              wfTagMeaningCtx_closure_body tm ctx result1 result1.qualType st1 st2 p tcls
                x body env x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
                hctxTm1 hresTm1 hetyp1 hmem_tcl hargTm'
          have hIH : wfTagMeaningCtx tm (ctxAfter bodyCtx result3) :=
            bodyIH fuel' (Nat.lt_succ_self _) bodyCtx body result3 hwf_body htcBody'
          show wfTagMeaningCtx tm (ctxAfter ctx _)
          unfold wfTagMeaningCtx at hctxTm1 hIH ⊢
          simp only [ctxAfter] at hctxTm1 hIH ⊢
          exact EnvRespectsTagMeaning_mix tm ctx.varEnv result1.memEnv'
            bodyCtx.varEnv result3.memEnv' hctxTm1 hIH
  | extern x retSpec effects capturedEnv =>
    cases fuel with
    | zero => simp [applyFnTClosure] at happly
    | succ fuel' =>
      simp only [applyFnTClosure] at happly
      have hioFree : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
      rw [hioFree] at happly
      simp only [ite_true] at happly; simp only [bind, Except.bind] at happly
      exact absurd happly (by simp)

lemma applyFnTClosure_ok_QTypRespectsTagMeaning_byIH
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (tcls : List FnTClosure)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (bodyIH :
    ∀ (fuel' : Nat), fuel' < fuel →
      ∀ (ctx : TypeContext) (e : Expr) (res : TypeResult),
      wfTagMeaningCtx tm ctx →
      typecheck .ioFree ctx e fuel' = .ok res →
      QTypRespectsTagMeaning tm res.qualType)
  (tcl : FnTClosure) (r : TypeResult)
  (hctxTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm1 : QTypRespectsTagMeaning tm result1.qualType)
  (hetyp1 : result1.qualType.etyp = ETyp.arrow st1 st2 p tcls)
  (hmem_tcl : tcl ∈ tcls)
  (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, argPoison, argPred⟩)
  (happly :
    applyFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel = .ok r) :
  QTypRespectsTagMeaning tm r.qualType := by
  cases tcl with
  | regular x body env =>
    cases fuel with
    | zero => simp [applyFnTClosure] at happly
    | succ fuel' =>
      simp only [applyFnTClosure, bind, Except.bind] at happly
      split at happly
      · exact absurd happly (Except.error_ne_ok _ _)
      · next result3 htcBody =>
        cases hqt3 : result3.qualType with
        | mk etyp3 p3 pred3 =>
        simp only [hqt3] at happly
        split at happly
        · simp at happly
        · next hsub =>
          simp only [pure, Except.pure] at happly
          cases happly
          set bodyCtx := { ctx with
              pc := joinPoison p (joinPoison p1 ctx.pc),
              memEnv := result1.memEnv',
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩,
              tagEnv := result1.tagEnv', nextTag := result1.nextTag',
              nextLoc := result1.nextLoc', regime := result1.regime' }
          have htcBody' : typecheck .ioFree bodyCtx body fuel' = .ok result3 := by
            simpa [typecheck] using htcBody
          have hargTm' : QTypRespectsTagMeaning tm ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩ :=
            QTypRespectsTagMeaning_transport_etyp_pred tm
              ⟨argEtyp, argPoison, argPred⟩ ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
              hargTm rfl rfl
          have hwf_body : wfTagMeaningCtx tm bodyCtx := by
            simpa [bodyCtx, ctxAfter] using
              wfTagMeaningCtx_closure_body tm ctx result1 result1.qualType st1 st2 p tcls
                x body env x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
                hctxTm1 hresTm1 hetyp1 hmem_tcl hargTm'
          have hresTm3 : QTypRespectsTagMeaning tm ⟨etyp3, p3, pred3⟩ := by
            rw [← hqt3]
            exact bodyIH fuel' (Nat.lt_succ_self _) bodyCtx body result3 hwf_body htcBody'
          simp only [normalizeAppResultByProvenance]
          split
          · intro q' k' d' hinq hgd
            exact QTypRespectsTagMeaning_of_etyp_noPred tm ⟨etyp3, p3, pred3⟩
              ⟨etyp3, true, Predicate.noPred⟩ hresTm3 rfl rfl hinq hgd
          · intro q' k' d' hinq hgd
            exact QTypRespectsTagMeaning_transport_etyp_pred tm ⟨etyp3, p3, pred3⟩
              ⟨etyp3, joinPoison p1 (joinPoison p p3), pred3⟩ hresTm3 rfl rfl hinq hgd
  | extern x retSpec effects capturedEnv =>
    cases fuel with
    | zero => simp [applyFnTClosure] at happly
    | succ fuel' =>
      simp only [applyFnTClosure] at happly
      have hioFree : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
      rw [hioFree] at happly
      simp only [ite_true] at happly; simp only [bind, Except.bind] at happly
      simp at happly

lemma mapM_applyFnTClosure_forall_wfTagMeaningCtx_byIH
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (tcls : List FnTClosure)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (results : List TypeResult)
  (bodyIH :
    ∀ (fuel' : Nat), fuel' < fuel →
      ∀ (ctx : TypeContext) (e : Expr) (res : TypeResult),
      wfTagMeaningCtx tm ctx →
      typecheck .ioFree ctx e fuel' = .ok res →
      wfTagMeaningCtx tm (ctxAfter ctx res))
  (hctxTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm1 : QTypRespectsTagMeaning tm result1.qualType)
  (hetyp1 : result1.qualType.etyp = ETyp.arrow st1 st2 p tcls)
  (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, argPoison, argPred⟩)
  (hmap :
    List.mapM
      (fun tcl => applyFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      tcls = .ok results) :
  ∀ r, r ∈ results → wfTagMeaningCtx tm (ctxAfter ctx r) := by
  intro r hr
  rcases list_mapM_ok_mem_output_exists_input
      (f := fun tcl => applyFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      (hmap := hmap) (hmem := hr) with
    ⟨tcl, htcl_mem, happly⟩
  exact
    applyFnTClosure_ok_wfTagMeaningCtx_byIH
      (tm := tm) (bodyIH := bodyIH)
      (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
      (tcls := tcls)
      (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
      (result1 := result1) (fuel := fuel) (tcl := tcl) (r := r)
      hctxTm1 hresTm1 hetyp1 htcl_mem hargTm happly

lemma mapM_applyFnTClosure_forall_QTypRespectsTagMeaning_byIH
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (tcls : List FnTClosure)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (results : List TypeResult)
  (bodyIH :
    ∀ (fuel' : Nat), fuel' < fuel →
      ∀ (ctx : TypeContext) (e : Expr) (res : TypeResult),
      wfTagMeaningCtx tm ctx →
      typecheck .ioFree ctx e fuel' = .ok res →
      QTypRespectsTagMeaning tm res.qualType)
  (hctxTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm1 : QTypRespectsTagMeaning tm result1.qualType)
  (hetyp1 : result1.qualType.etyp = ETyp.arrow st1 st2 p tcls)
  (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, argPoison, argPred⟩)
  (hmap :
    List.mapM
      (fun tcl => applyFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      tcls = .ok results) :
  ∀ r, r ∈ results → QTypRespectsTagMeaning tm r.qualType := by
  intro r hr
  rcases list_mapM_ok_mem_output_exists_input
      (f := fun tcl => applyFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      (hmap := hmap) (hmem := hr) with
    ⟨tcl, htcl_mem, happly⟩
  exact
    applyFnTClosure_ok_QTypRespectsTagMeaning_byIH
      (tm := tm) (bodyIH := bodyIH)
      (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
      (tcls := tcls)
      (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
      (result1 := result1) (fuel := fuel) (tcl := tcl) (r := r)
      hctxTm1 hresTm1 hetyp1 htcl_mem hargTm happly

lemma applyPFnTClosure_ok_wfTagMeaningCtx_byIH
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (tcls : List PFnTClosure)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (bodyIH :
    ∀ (fuel' : Nat), fuel' < fuel →
      ∀ (ctx : TypeContext) (e : Expr) (res : TypeResult),
      wfTagMeaningCtx tm ctx →
      typecheck .ioFree ctx e fuel' = .ok res →
      wfTagMeaningCtx tm (ctxAfter ctx res))
  (tcl : PFnTClosure) (r : TypeResult)
  (hctxTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm1 : QTypRespectsTagMeaning tm result1.qualType)
  (hetyp1 : result1.qualType.etyp = ETyp.parrow st1 st2 p tcls)
  (hmem_tcl : tcl ∈ tcls)
  (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, argPoison, argPred⟩)
  (happly :
    applyPFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel = .ok r) :
  wfTagMeaningCtx tm (ctxAfter ctx r) := by
  cases tcl with
  | regular x body env =>
    cases fuel with
    | zero => simp [applyPFnTClosure] at happly
    | succ fuel' =>
      simp only [applyPFnTClosure, bind, Except.bind] at happly
      split at happly
      · exact absurd happly (Except.error_ne_ok _ _)
      · next result3 htcBody =>
        cases hqt3 : result3.qualType with
        | mk etyp3 p3 pred3 =>
        simp only [hqt3] at happly
        split at happly
        · simp at happly
        · next hsub =>
          simp only [pure, Except.pure] at happly
          cases happly
          set bodyCtx := { ctx with
              pc := joinPoison p (joinPoison ctx.pc p1),
              memEnv := result1.memEnv',
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩,
              tagEnv := result1.tagEnv', nextTag := result1.nextTag',
              pureCtx := true,
              nextLoc := result1.nextLoc', regime := result1.regime' }
          have htcBody' : typecheck .ioFree bodyCtx (PExpr.toExpr body) fuel' = .ok result3 := by
            simpa [typecheck] using htcBody
          have hargTm' : QTypRespectsTagMeaning tm ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩ :=
            QTypRespectsTagMeaning_transport_etyp_pred tm
              ⟨argEtyp, argPoison, argPred⟩ ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
              hargTm rfl rfl
          have hwf_body : wfTagMeaningCtx tm bodyCtx := by
            simpa [bodyCtx, ctxAfter] using
              wfTagMeaningCtx_pclosure_body tm ctx result1 result1.qualType st1 st2 p tcls
                x body env x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
                hctxTm1 hresTm1 hetyp1 hmem_tcl hargTm'
          have hIH : wfTagMeaningCtx tm (ctxAfter bodyCtx result3) :=
            bodyIH fuel' (Nat.lt_succ_self _) bodyCtx (PExpr.toExpr body) result3 hwf_body htcBody'
          show wfTagMeaningCtx tm (ctxAfter ctx _)
          unfold wfTagMeaningCtx at hctxTm1 hIH ⊢
          simp only [ctxAfter] at hctxTm1 hIH ⊢
          exact EnvRespectsTagMeaning_mix tm ctx.varEnv result1.memEnv'
            bodyCtx.varEnv result3.memEnv' hctxTm1 hIH
  | extern x retSpec capturedEnv =>
    cases fuel with
    | zero => simp [applyPFnTClosure] at happly
    | succ fuel' =>
      simp only [applyPFnTClosure] at happly
      have hioFree : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
      rw [hioFree] at happly
      simp only [ite_true] at happly; simp only [bind, Except.bind] at happly
      exact absurd happly (by simp)

lemma applyPFnTClosure_ok_QTypRespectsTagMeaning_byIH
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (tcls : List PFnTClosure)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (bodyIH :
    ∀ (fuel' : Nat), fuel' < fuel →
      ∀ (ctx : TypeContext) (e : Expr) (res : TypeResult),
      wfTagMeaningCtx tm ctx →
      typecheck .ioFree ctx e fuel' = .ok res →
      QTypRespectsTagMeaning tm res.qualType)
  (tcl : PFnTClosure) (r : TypeResult)
  (hctxTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm1 : QTypRespectsTagMeaning tm result1.qualType)
  (hetyp1 : result1.qualType.etyp = ETyp.parrow st1 st2 p tcls)
  (hmem_tcl : tcl ∈ tcls)
  (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, argPoison, argPred⟩)
  (happly :
    applyPFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel = .ok r) :
  QTypRespectsTagMeaning tm r.qualType := by
  cases tcl with
  | regular x body env =>
    cases fuel with
    | zero => simp [applyPFnTClosure] at happly
    | succ fuel' =>
      simp only [applyPFnTClosure, bind, Except.bind] at happly
      split at happly
      · exact absurd happly (Except.error_ne_ok _ _)
      · next result3 htcBody =>
        cases hqt3 : result3.qualType with
        | mk etyp3 p3 pred3 =>
        simp only [hqt3] at happly
        split at happly
        · simp at happly
        · next hsub =>
          simp only [pure, Except.pure] at happly
          cases happly
          set bodyCtx := { ctx with
              pc := joinPoison p (joinPoison ctx.pc p1),
              memEnv := result1.memEnv',
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩,
              tagEnv := result1.tagEnv', nextTag := result1.nextTag',
              pureCtx := true,
              nextLoc := result1.nextLoc', regime := result1.regime' }
          have htcBody' : typecheck .ioFree bodyCtx (PExpr.toExpr body) fuel' = .ok result3 := by
            simpa [typecheck] using htcBody
          have hargTm' : QTypRespectsTagMeaning tm ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩ :=
            QTypRespectsTagMeaning_transport_etyp_pred tm
              ⟨argEtyp, argPoison, argPred⟩ ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
              hargTm rfl rfl
          have hwf_body : wfTagMeaningCtx tm bodyCtx := by
            simpa [bodyCtx, ctxAfter] using
              wfTagMeaningCtx_pclosure_body tm ctx result1 result1.qualType st1 st2 p tcls
                x body env x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
                hctxTm1 hresTm1 hetyp1 hmem_tcl hargTm'
          have hresTm3 : QTypRespectsTagMeaning tm ⟨etyp3, p3, pred3⟩ := by
            rw [← hqt3]
            exact bodyIH fuel' (Nat.lt_succ_self _) bodyCtx (PExpr.toExpr body) result3 hwf_body htcBody'
          simp only [normalizeAppResultByProvenance]
          split
          · intro q' k' d' hinq hgd
            exact QTypRespectsTagMeaning_of_etyp_noPred tm ⟨etyp3, p3, pred3⟩
              ⟨etyp3, true, Predicate.noPred⟩ hresTm3 rfl rfl hinq hgd
          · intro q' k' d' hinq hgd
            exact QTypRespectsTagMeaning_transport_etyp_pred tm ⟨etyp3, p3, pred3⟩
              ⟨etyp3, joinPoison p1 (joinPoison p p3), pred3⟩ hresTm3 rfl rfl hinq hgd
  | extern x retSpec capturedEnv =>
    cases fuel with
    | zero => simp [applyPFnTClosure] at happly
    | succ fuel' =>
      simp only [applyPFnTClosure] at happly
      have hioFree : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
      rw [hioFree] at happly
      simp only [ite_true] at happly; simp only [bind, Except.bind] at happly
      simp at happly

lemma mapM_applyPFnTClosure_forall_wfTagMeaningCtx_byIH
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (tcls : List PFnTClosure)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (results : List TypeResult)
  (bodyIH :
    ∀ (fuel' : Nat), fuel' < fuel →
      ∀ (ctx : TypeContext) (e : Expr) (res : TypeResult),
      wfTagMeaningCtx tm ctx →
      typecheck .ioFree ctx e fuel' = .ok res →
      wfTagMeaningCtx tm (ctxAfter ctx res))
  (hctxTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm1 : QTypRespectsTagMeaning tm result1.qualType)
  (hetyp1 : result1.qualType.etyp = ETyp.parrow st1 st2 p tcls)
  (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, argPoison, argPred⟩)
  (hmap :
    List.mapM
      (fun tcl => applyPFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      tcls = .ok results) :
  ∀ r, r ∈ results → wfTagMeaningCtx tm (ctxAfter ctx r) := by
  intro r hr
  rcases list_mapM_ok_mem_output_exists_input
      (f := fun tcl => applyPFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      (hmap := hmap) (hmem := hr) with
    ⟨tcl, htcl_mem, happly⟩
  exact
    applyPFnTClosure_ok_wfTagMeaningCtx_byIH
      (tm := tm) (bodyIH := bodyIH)
      (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
      (tcls := tcls)
      (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
      (result1 := result1) (fuel := fuel) (tcl := tcl) (r := r)
      hctxTm1 hresTm1 hetyp1 htcl_mem hargTm happly

lemma mapM_applyPFnTClosure_forall_QTypRespectsTagMeaning_byIH
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (tcls : List PFnTClosure)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (results : List TypeResult)
  (bodyIH :
    ∀ (fuel' : Nat), fuel' < fuel →
      ∀ (ctx : TypeContext) (e : Expr) (res : TypeResult),
      wfTagMeaningCtx tm ctx →
      typecheck .ioFree ctx e fuel' = .ok res →
      QTypRespectsTagMeaning tm res.qualType)
  (hctxTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm1 : QTypRespectsTagMeaning tm result1.qualType)
  (hetyp1 : result1.qualType.etyp = ETyp.parrow st1 st2 p tcls)
  (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, argPoison, argPred⟩)
  (hmap :
    List.mapM
      (fun tcl => applyPFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      tcls = .ok results) :
  ∀ r, r ∈ results → QTypRespectsTagMeaning tm r.qualType := by
  intro r hr
  rcases list_mapM_ok_mem_output_exists_input
      (f := fun tcl => applyPFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      (hmap := hmap) (hmem := hr) with
    ⟨tcl, htcl_mem, happly⟩
  exact
    applyPFnTClosure_ok_QTypRespectsTagMeaning_byIH
      (tm := tm) (bodyIH := bodyIH)
      (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
      (tcls := tcls)
      (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
      (result1 := result1) (fuel := fuel) (tcl := tcl) (r := r)
      hctxTm1 hresTm1 hetyp1 htcl_mem hargTm happly

lemma join_transport_wfTagMeaningCtx_byFirst
  (tm : TagMeaning) (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (h_first : wfTagMeaningCtx tm (ctxAfter ctx first)) :
  wfTagMeaningCtx tm (ctxAfter ctx res) := by
  unfold wfTagMeaningCtx
  rw [ctxAfter]
  have h_first_env : EnvRespectsTagMeaning tm ctx.varEnv first.memEnv' := by
    simpa [wfTagMeaningCtx, ctxAfter] using h_first
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
        TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvsStrong acc.2.1 result.memEnv',
              joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred,
              joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 result.regime',
              max acc.2.2.2.2.2.2.1 result.nextLoc',
              max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_tm :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        EnvRespectsTagMeaning tm ctx.varEnv acc.2.1 →
        EnvRespectsTagMeaning tm ctx.varEnv acc'.2.1 := by
    intro rs' acc acc' hfold hacc
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        cases hfold
        exact hacc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hacc1 : EnvRespectsTagMeaning tm ctx.varEnv (joinMemEnvsStrong acc.2.1 x.memEnv') :=
              EnvRespectsTagMeaning_joinMemEnvsStrong' tm ctx.varEnv acc.2.1 x.memEnv' hacc
            exact ih _ hfold hacc1
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at _h_join
      cases hcheck :
          (List.foldlM
            (fun x result =>
              match result.qualType with
              | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                if beqETypSignature etyp resEtyp = false then
                  Except.error
                    (toString "Closure alternatives produced incompatible result types: " ++ toString (repr etyp) ++
                        toString " vs " ++ toString (repr resEtyp))
                else Except.ok ())
            () rest : Except String Unit) with
      | error err =>
          erw [hcheck] at _h_join
          simp at _h_join
      | ok _ =>
          erw [hcheck] at _h_join
          simp at _h_join
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc', first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              exact h_fold_tm rest
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc', first.nextTag')
                a hfold h_first_env

lemma QTypRespectsTagMeaning_sub_byJoin
    (tm : TagMeaning) {qt qt' : QTyp}
    (h : QTypRespectsTagMeaning tm qt) (hinq : QTypInQTyp qt' qt) :
    QTypRespectsTagMeaning tm qt' :=
  fun hinq'' hqd => h (QTypInQTyp.trans _ qt' qt hinq'' hinq) hqd

lemma joinTypeResults_QTypRespectsTagMeaning_byMembers
  (tm : TagMeaning)
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (h_join : joinTypeResults ctx first rest = .ok res)
  (h_first : QTypRespectsTagMeaning tm first.qualType)
  (h_rest : ∀ r ∈ rest, QTypRespectsTagMeaning tm r.qualType) :
  QTypRespectsTagMeaning tm res.qualType := by
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
        TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvsStrong acc.2.1 result.memEnv',
              joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred,
              joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 result.regime',
              max acc.2.2.2.2.2.2.1 result.nextLoc',
              max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_qtm :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        QTypRespectsTagMeaning tm ⟨acc.1, acc.2.2.1, acc.2.2.2.1⟩ →
        (∀ r ∈ rs', QTypRespectsTagMeaning tm r.qualType) →
        QTypRespectsTagMeaning tm ⟨acc'.1, acc'.2.2.1, acc'.2.2.2.1⟩ := by
    intro rs' acc acc' hfold hacc hrs
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        cases hfold; exact hacc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv',
                joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred,
                joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc',
                max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have hx : QTypRespectsTagMeaning tm x.qualType := hrs x (by simp)
            have hacc1 : QTypRespectsTagMeaning tm ⟨acc1.1, acc1.2.2.1, acc1.2.2.2.1⟩ :=
              QTypRespectsTagMeaning_joinStep tm acc.1 resEtyp acc.2.2.1 resPoison
                acc.2.2.2.1 resPred hacc (hqx ▸ hx)
            have hrs_tail : ∀ r ∈ xs, QTypRespectsTagMeaning tm r.qualType := by
              intro r hr; exact hrs r (by simp [hr])
            show QTypRespectsTagMeaning tm ⟨acc'.1, acc'.2.2.1, acc'.2.2.2.1⟩
            exact ih (acc := acc1) hfold_tail hacc1 hrs_tail
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at h_join
      cases hcheck :
          (List.foldlM
            (fun x result =>
              match result.qualType with
              | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                if beqETypSignature etyp resEtyp = false then
                  Except.error
                    (toString "Closure alternatives produced incompatible result types: " ++
                      toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
                else Except.ok ())
            () rest : Except String Unit) with
      | error _ => erw [hcheck] at h_join; simp at h_join
      | ok _ =>
          erw [hcheck] at h_join; simp at h_join
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                  first.nextLoc', first.nextTag') rest with
          | error _ => erw [hfold] at h_join; simp at h_join
          | ok a =>
              rcases a with
                ⟨joinedEtyp, joinedMemEnv, joinedPoison, joinedPred,
                  joinedTagEnv, joinedRegime, maxNextLoc, maxNextTag⟩
              erw [hfold] at h_join
              simp at h_join
              subst res
              have h_first_qtm : QTypRespectsTagMeaning tm ⟨etyp, poison, pred⟩ :=
                hqt ▸ h_first
              have hacc_qtm :
                  QTypRespectsTagMeaning tm ⟨joinedEtyp, joinedPoison, joinedPred⟩ :=
                h_fold_qtm rest
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                    first.nextLoc', first.nextTag')
                  (joinedEtyp, joinedMemEnv, joinedPoison, joinedPred,
                    joinedTagEnv, joinedRegime, maxNextLoc, maxNextTag)
                  hfold h_first_qtm h_rest
              cases joinedEtyp with
              | arrow st1 st2 p tcls =>
                  intro qt' k d hinq hqd
                  exact
                    QTypRespectsTagMeaning_of_etyp_noPred tm
                      ⟨ETyp.arrow st1 st2 p tcls, joinedPoison, joinedPred⟩
                      ⟨ETyp.arrow st1 st2 p tcls, joinPoison ctx.pc joinedPoison, Predicate.noPred⟩
                      hacc_qtm rfl rfl hinq hqd
              | parrow st1 st2 p tcls =>
                  intro qt' k d hinq hqd
                  exact
                    QTypRespectsTagMeaning_of_etyp_noPred tm
                      ⟨ETyp.parrow st1 st2 p tcls, joinedPoison, joinedPred⟩
                      ⟨ETyp.parrow st1 st2 p tcls, joinPoison ctx.pc joinedPoison, Predicate.noPred⟩
                      hacc_qtm rfl rfl hinq hqd
              | int =>
                  intro qt' k d hinq hqd
                  exact
                    QTypRespectsTagMeaning_transport_etyp_pred tm
                      ⟨ETyp.int, joinedPoison, joinedPred⟩
                      ⟨ETyp.int, joinPoison ctx.pc joinedPoison, joinedPred⟩
                      hacc_qtm rfl rfl hinq hqd
              | bool =>
                  intro qt' k d hinq hqd
                  exact
                    QTypRespectsTagMeaning_transport_etyp_pred tm
                      ⟨ETyp.bool, joinedPoison, joinedPred⟩
                      ⟨ETyp.bool, joinPoison ctx.pc joinedPoison, joinedPred⟩
                      hacc_qtm rfl rfl hinq hqd
              | unit =>
                  intro qt' k d hinq hqd
                  exact
                    QTypRespectsTagMeaning_transport_etyp_pred tm
                      ⟨ETyp.unit, joinedPoison, joinedPred⟩
                      ⟨ETyp.unit, joinPoison ctx.pc joinedPoison, joinedPred⟩
                      hacc_qtm rfl rfl hinq hqd
              | string =>
                  intro qt' k d hinq hqd
                  exact
                    QTypRespectsTagMeaning_transport_etyp_pred tm
                      ⟨ETyp.string, joinedPoison, joinedPred⟩
                      ⟨ETyp.string, joinPoison ctx.pc joinedPoison, joinedPred⟩
                      hacc_qtm rfl rfl hinq hqd
              | ref ls =>
                  intro qt' k d hinq hqd
                  exact
                    QTypRespectsTagMeaning_transport_etyp_pred tm
                      ⟨ETyp.ref ls, joinedPoison, joinedPred⟩
                      ⟨ETyp.ref ls, joinPoison ctx.pc joinedPoison, joinedPred⟩
                      hacc_qtm rfl rfl hinq hqd

/-- Body typecheck preserves wfTagMeaningCtx (fuel induction).
    wfTagMeaningCtx tm ctx = EnvRespectsTagMeaning tm ctx.varEnv ctx.memEnv, so we need
    to show that after typechecking, all guard descriptors in (ctx.varEnv, res.memEnv')
    are in tm. Since ctxAfter preserves varEnv, the varEnv side is automatic. For memEnv,
    we track how each expression form transforms memEnv and use join/update lemmas. -/

lemma typecheckExpr_preserves_wfTagMeaningCtx_main :
    ∀ (fuel : Nat) (tm : TagMeaning) (ctx : TypeContext) (e : Expr) (res : TypeResult),
    wfTagMeaningCtx tm ctx →
    typecheck .ioFree ctx e fuel = .ok res →
    wfTagMeaningCtx tm (ctxAfter ctx res) ∧ QTypRespectsTagMeaning tm res.qualType := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
    intro tm ctx e res hwf htc
    have IH_wf : ∀ m < fuel, ∀ (tm' : TagMeaning) (ctx' : TypeContext) (e' : Expr) (res' : TypeResult),
        wfTagMeaningCtx tm' ctx' →
        typecheck .ioFree ctx' e' m = .ok res' →
        wfTagMeaningCtx tm' (ctxAfter ctx' res') := by
      intro m hm tm' ctx' e' res' hwf' htc'; exact (IH m hm tm' ctx' e' res' hwf' htc').1
    have IH_qt : ∀ m < fuel, ∀ (tm' : TagMeaning) (ctx' : TypeContext) (e' : Expr) (res' : TypeResult),
        wfTagMeaningCtx tm' ctx' →
        typecheck .ioFree ctx' e' m = .ok res' →
        QTypRespectsTagMeaning tm' res'.qualType := by
      intro m hm tm' ctx' e' res' hwf' htc'; exact (IH m hm tm' ctx' e' res' hwf' htc').2
    unfold typecheck at htc
    cases fuel with
    | zero =>
        unfold typecheckExpr at htc; simp at htc
    | succ fuel' =>
        unfold typecheckExpr at htc
        cases e with
        -- ===== Trivial cases: memEnv unchanged (ctxAfter preserves both varEnv and memEnv) =====
        -- Result qualType has noPred + non-function etyp → QTypRespectsTagMeaning vacuous
        | num _n =>
            unfold typecheckInt at htc; simp [pure, Except.pure] at htc; cases htc
            refine ⟨by simpa [wfTagMeaningCtx, ctxAfter], ?_⟩
            exact QTypRespectsTagMeaning_of_nonFunction_noGuard tm _ rfl rfl
        | bool _b =>
            unfold typecheckBool at htc; simp [pure, Except.pure] at htc; cases htc
            refine ⟨by simpa [wfTagMeaningCtx, ctxAfter], ?_⟩
            exact QTypRespectsTagMeaning_of_nonFunction_noGuard tm _ rfl rfl
        | unit =>
            unfold typecheckUnit at htc; simp [pure, Except.pure] at htc; cases htc
            refine ⟨by simpa [wfTagMeaningCtx, ctxAfter], ?_⟩
            exact QTypRespectsTagMeaning_of_nonFunction_noGuard tm _ rfl rfl
        | str _s =>
            unfold typecheckString at htc; simp [pure, Except.pure] at htc; cases htc
            refine ⟨by simpa [wfTagMeaningCtx, ctxAfter], ?_⟩
            exact QTypRespectsTagMeaning_of_nonFunction_noGuard tm _ rfl rfl
        | var x =>
            -- typecheckVar always returns memEnv' = ctx.memEnv
            simp at htc
            unfold typecheckVar at htc
            simp only [bind, Except.bind] at htc
            cases hlookup : ctx.varEnv.lookup x with
            | none => simp [hlookup] at htc
            | some qt =>
              simp [hlookup] at htc
              cases qt with
              | mk etyp poison pred =>
                simp at htc
                -- All var sub-cases have non-function etyp (function case errors) and
                -- result pred ∈ {noPred, guardOnly k} → qtypGuardDesc? = none → QTypRespects vacuous
                cases pred with
                | noPred =>
                  simp [pure, Except.pure] at htc; cases htc
                  refine ⟨?_, ?_⟩
                  · simpa [wfTagMeaningCtx, ctxAfter]
                  · exact QTypRespectsTagMeaning_transport_etyp_noGuard tm
                      ⟨etyp, poison, Predicate.noPred⟩ _
                      (wfTagMeaningCtx_var_lookup_qtyp tm ctx x _ hwf hlookup)
                      (by simp) (by simp [qtypGuardDesc?])
                | guardOnly k =>
                  simp at htc
                  cases hfn : etyp.isFunctionType with
                  | false =>
                    simp [hfn] at htc
                    revert htc; generalize ctx.tagEnv[k]? = tv
                    cases tv with
                    | none => intro htc; simp at htc; cases htc
                              exact ⟨by simpa [wfTagMeaningCtx, ctxAfter],
                                QTypRespectsTagMeaning_of_nonFunction_noGuard tm _ hfn (by simp [qtypGuardDesc?])⟩
                    | some tv => cases tv with | mk val deps =>
                      cases val <;> intro htc <;> simp at htc <;> cases htc <;>
                        exact ⟨by simpa [wfTagMeaningCtx, ctxAfter],
                          QTypRespectsTagMeaning_of_nonFunction_noGuard tm _ hfn (by simp [qtypGuardDesc?])⟩
                  | true => simp [hfn] at htc
                | guardClosure k tcls ptcls body_t =>
                  simp at htc
                  cases hfn : etyp.isFunctionType with
                  | false =>
                    simp [hfn] at htc
                    have hqt_orig : QTypRespectsTagMeaning tm ⟨etyp, poison, Predicate.guardClosure k tcls ptcls body_t⟩ :=
                      wfTagMeaningCtx_var_lookup_qtyp tm ctx x _ hwf hlookup
                    revert htc; generalize ctx.tagEnv[k]? = tv
                    cases tv with
                    | none => intro htc; simp at htc; cases htc
                              -- pred preserved as guardClosure — transport from original var binding
                              exact ⟨by simpa [wfTagMeaningCtx, ctxAfter],
                                QTypRespectsTagMeaning_transport_etyp_pred tm
                                  ⟨etyp, poison, Predicate.guardClosure k tcls ptcls body_t⟩
                                  ⟨etyp, joinPoison ctx.pc poison, Predicate.guardClosure k tcls ptcls body_t⟩
                                  hqt_orig rfl rfl⟩
                    | some tv => cases tv with | mk val deps =>
                      -- true/false → result pred = noPred
                      cases val <;> intro htc <;> simp at htc <;> cases htc <;>
                        exact ⟨by simpa [wfTagMeaningCtx, ctxAfter],
                          QTypRespectsTagMeaning_of_nonFunction_noGuard tm _ hfn (by simp [qtypGuardDesc?])⟩
                  | true => simp [hfn] at htc
        | fn x st1 body st2 =>
            unfold typecheckFn at htc; simp [pure, Except.pure] at htc; cases htc
            exact ⟨by simpa [wfTagMeaningCtx, ctxAfter],
              QTypRespectsTagMeaning_fn_regular tm ctx x st1 st2 ctx.pc body hwf⟩
        | pfn x st1 body st2 =>
            unfold typecheckPfn at htc
            simp [bind, Except.bind] at htc
            cases h_topexpr : body.toPExpr with
            | error _ => simp [h_topexpr] at htc
            | ok pbody =>
              simp [h_topexpr, pure, Except.pure] at htc; subst htc
              exact ⟨by simpa [wfTagMeaningCtx, ctxAfter],
                QTypRespectsTagMeaning_pfn_regular tm ctx x st1 st2 ctx.pc pbody hwf⟩
        -- Impossible in ioFree mode
        | externVal _ _ _ =>
            exfalso; simp at htc; unfold typecheckExternVal at htc
            have heq : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
            simp only [heq, ite_true, bind, Except.bind] at htc
            exact absurd htc (Except.error_ne_ok _ _)
        | externFn _ _ _ _ =>
            exfalso; simp at htc; unfold typecheckExternFn at htc
            have heq : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
            simp only [heq, ite_true, bind, Except.bind] at htc
            exact absurd htc (Except.error_ne_ok _ _)
        | externPfn _ _ _ =>
            exfalso; simp at htc; unfold typecheckExternPfn at htc
            have heq : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
            simp only [heq, ite_true, bind, Except.bind] at htc
            exact absurd htc (Except.error_ne_ok _ _)
        | rand _ =>
            simp at htc
            exact absurd htc (typecheckRand_ioFree_impossible ctx _ fuel' res)
        | frand _ =>
            simp at htc
            exact absurd htc (typecheckFrand_ioFree_impossible ctx _ fuel' res)
        | printInt _ =>
            simp at htc
            exact absurd htc (typecheckPrintInt_ioFree_impossible ctx _ fuel' res)
        | printString _ =>
            simp at htc
            exact absurd htc (typecheckPrintString_ioFree_impossible ctx _ fuel' res)
        -- ===== Single-IH cases: memEnv from sub-expression =====
        | unaryop op e1 =>
            have hstruct := typecheckUnaryOp_structure ctx op e1 fuel' res htc
            rcases hstruct with ⟨result1, result_etyp, htc1, _hopEtyp, hmemEnv, _, _, _, _, hetyp, _, hpred⟩
            have htc1' : typecheck .ioFree ctx e1 (fuel' - 1) = .ok result1 := by simpa using htc1
            have hIH := IH_wf (fuel' - 1) (by omega) tm ctx e1 result1 hwf htc1'
            refine ⟨?_, ?_⟩
            · simpa [wfTagMeaningCtx, ctxAfter, hmemEnv] using hIH
            · -- result_etyp from opUnaryEType? is always non-function (bool)
              have hnf : result_etyp.isFunctionType = false := by
                have : result_etyp = .bool := by
                  revert _hopEtyp; unfold opUnaryEType?; split <;> simp [eq_comm]
                subst this; decide
              apply QTypRespectsTagMeaning_of_nonFunction_noGuard
              · rw [hetyp]; exact hnf
              · simp [qtypGuardDesc?, hpred]
        | deref e1 =>
            cases fuel' with
            | zero =>
                simp [typecheckDeref] at htc
            | succ fuel'' =>
                have hstruct := typecheckDeref_structure ctx e1 (Nat.succ fuel'') res htc
                rcases hstruct with ⟨result1, htc1, hmem, _, _, _, _⟩
                have htc1' : typecheck .ioFree ctx e1 fuel'' = .ok result1 := by
                  simpa [typecheck] using htc1
                have hIH_wf := IH_wf fuel'' (by omega) tm ctx e1 result1 hwf htc1'
                refine ⟨?_, ?_⟩
                · simpa [wfTagMeaningCtx, ctxAfter, hmem] using hIH_wf
                · exact
                    typecheckDeref_qtypRespects tm ctx e1 fuel'' res result1
                      (by simpa [ctxAfter] using hIH_wf)
                      (by simpa using htc1) htc
        -- ===== Double-IH cases: memEnv chains through sub-expressions =====
        | op e1 _op e2 =>
            have hstruct := typecheckOp_structure ctx e1 e2 _op fuel' res htc
            rcases hstruct with ⟨result1, result2, result_etyp, htc1, htc2, _hopEtyp, hmemEnv, _, _, _, _, hetyp, _, hpred⟩
            have htc1' : typecheck .ioFree ctx e1 (fuel' - 1) = .ok result1 := by simpa using htc1
            have hIH1 := IH_wf (fuel' - 1) (by omega) tm ctx e1 result1 hwf htc1'
            have hwf_mid : wfTagMeaningCtx tm (updateCtxFromResult ctx result1) := by
              simpa [wfTagMeaningCtx, ctxAfter, updateCtxFromResult] using hIH1
            have htc2' : typecheck .ioFree (updateCtxFromResult ctx result1) e2 (fuel' - 1) = .ok result2 := by simpa using htc2
            have hIH2 := IH_wf (fuel' - 1) (by omega) tm (updateCtxFromResult ctx result1) e2 result2 hwf_mid htc2'
            refine ⟨?_, ?_⟩
            · simpa [wfTagMeaningCtx, ctxAfter, updateCtxFromResult, hmemEnv] using hIH2
            · -- result_etyp from opEType? is always non-function (int/bool/float/string)
              have hnf : result_etyp.isFunctionType = false := by
                have : result_etyp = .int ∨ result_etyp = .bool := by
                  revert _hopEtyp; unfold opEType?; split <;> simp [eq_comm] <;> tauto
                rcases this with rfl | rfl <;> decide
              apply QTypRespectsTagMeaning_of_nonFunction_noGuard
              · rw [hetyp]; exact hnf
              · simp [qtypGuardDesc?, hpred]
        | seq e1 e2 =>
            have hstruct := typecheckSeq_structure ctx e1 e2 fuel' res htc
            rcases hstruct with ⟨result1, ctx', htc1, hctx', htc2⟩
            have htc1' : typecheck .ioFree ctx e1 (fuel' - 1) = .ok result1 := by simpa using htc1
            have hIH1 := IH_wf (fuel' - 1) (by omega) tm ctx e1 result1 hwf htc1'
            have hwf_mid : wfTagMeaningCtx tm ctx' := by
              rw [hctx']
              simpa [wfTagMeaningCtx, ctxAfter, updateCtxFromResult] using hIH1
            have htc2' : typecheck .ioFree ctx' e2 (fuel' - 1) = .ok res := by simpa using htc2
            -- IH on e2 gives both parts: wfTagMeaningCtx and QTypRespectsTagMeaning
            have hIH2_wf := IH_wf (fuel' - 1) (by omega) tm ctx' e2 res hwf_mid htc2'
            have hIH2_qt : QTypRespectsTagMeaning tm res.qualType :=
              IH_qt (fuel' - 1) (by omega) tm ctx' e2 res hwf_mid htc2'
            exact ⟨by simpa [wfTagMeaningCtx, ctxAfter, updateCtxFromResult, hctx'] using hIH2_wf,
                   hIH2_qt⟩
        | vlet x e1 e2 =>
            have hstruct := typecheckVlet_structure ctx x e1 e2 fuel' res htc
            rcases hstruct with ⟨result1, result2, ctx', htc1, hctx', htc2, hetyp_res, hmemEnv, _, _, _, _, _, hpred_res⟩
            have htc1' : typecheck .ioFree ctx e1 (fuel' - 1) = .ok result1 := by simpa using htc1
            have hIH1_wf := IH_wf (fuel' - 1) (by omega) tm ctx e1 result1 hwf htc1'
            have hIH1_qt : QTypRespectsTagMeaning tm result1.qualType :=
              IH_qt (fuel' - 1) (by omega) tm ctx e1 result1 hwf htc1'
            -- ctx' extends varEnv with x ↦ result1.qualType. Use IH_qt for the new binding.
            have hwf_mid : wfTagMeaningCtx tm ctx' := by
              rw [hctx']
              have hwf_after : wfTagMeaningCtx tm (ctxAfter ctx result1) := hIH1_wf
              simp only [wfTagMeaningCtx, ctxAfter] at hwf_after
              let ctxBase : TypeContext :=
                ⟨ctx.pc, result1.regime', result1.memEnv', ctx.varEnv, result1.tagEnv',
                 result1.nextLoc', result1.nextTag', ctx.pureCtx⟩
              exact wfTagMeaningCtx_varEnv_ext tm ctxBase x result1.qualType
                (by simpa [wfTagMeaningCtx, ctxAfter, ctxBase] using hwf_after)
                hIH1_qt
            have htc2' : typecheck .ioFree ctx' e2 (fuel' - 1) = .ok result2 := by simpa using htc2
            have hIH2_wf := IH_wf (fuel' - 1) (by omega) tm ctx' e2 result2 hwf_mid htc2'
            have hIH2_qt : QTypRespectsTagMeaning tm result2.qualType :=
              IH_qt (fuel' - 1) (by omega) tm ctx' e2 result2 hwf_mid htc2'
            refine ⟨?_, ?_⟩
            · -- wfTagMeaningCtx: mix varEnv from hwf, memEnv from IH2
              simp only [wfTagMeaningCtx, ctxAfter]
              rw [hmemEnv]
              have hIH2' : EnvRespectsTagMeaning tm ctx'.varEnv result2.memEnv' := by
                simpa [wfTagMeaningCtx, ctxAfter] using hIH2_wf
              exact EnvRespectsTagMeaning_mix tm ctx.varEnv ctx.memEnv ctx'.varEnv result2.memEnv' hwf hIH2'
            · -- QTypRespectsTagMeaning: res.qualType has same etyp and pred as result2.qualType
              exact QTypRespectsTagMeaning_transport_etyp_pred tm result2.qualType res.qualType
                hIH2_qt (by rw [hetyp_res]) (by rw [hpred_res])
        -- ===== Memory update cases =====
        | newRef e1 =>
            have hstruct := typecheckNewRef_structure ctx e1 fuel' res htc
            rcases hstruct with
              ⟨result1, l, htc1, hl, hInt, hRef_res, _hpoison_res, hpred_res, hmem_res,
                _htag_res, _hnextLoc_res, _hnextTag_res, _hregime_res⟩
            have htc1' : typecheck .ioFree ctx e1 (fuel' - 1) = .ok result1 := by
              simpa using htc1
            have hIH1_wf := IH_wf (fuel' - 1) (by omega) tm ctx e1 result1 hwf htc1'
            have hIH1_qt : QTypRespectsTagMeaning tm result1.qualType :=
              IH_qt (fuel' - 1) (by omega) tm ctx e1 result1 hwf htc1'
            refine ⟨?_, ?_⟩
            · let storedQt : QTyp :=
                ⟨ETyp.int, joinPoison ctx.pc result1.qualType.poison,
                  if ctx.pc then Predicate.noPred else result1.qualType.pred⟩
              have hEnv1 : EnvRespectsTagMeaning tm ctx.varEnv result1.memEnv' := by
                simpa [wfTagMeaningCtx, ctxAfter] using hIH1_wf
              have hstored_qtm : QTypRespectsTagMeaning tm storedQt := by
                by_cases hpc : ctx.pc = true
                · have hnotfun : storedQt.etyp.isFunctionType = false := by
                    simp [storedQt, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                  have hguard : qtypGuardDesc? storedQt = none := by
                    simp [storedQt, hpc, qtypGuardDesc?]
                  exact QTypRespectsTagMeaning_of_nonFunction_noGuard tm storedQt hnotfun hguard
                · exact
                    QTypRespectsTagMeaning_transport_etyp_pred tm result1.qualType storedQt
                      hIH1_qt
                      (by simpa [storedQt] using hInt.symm)
                      (by simp [storedQt, hpc])
              have hEnv_res : EnvRespectsTagMeaning tm ctx.varEnv res.memEnv' := by
                rw [hmem_res, hl]
                exact
                  EnvRespectsTagMeaning_updateMemEnv
                    tm ctx.varEnv result1.memEnv' result1.nextLoc' storedQt rfl hEnv1 hstored_qtm
              exact wfTagMeaningCtx_ctxAfter tm ctx res hEnv_res
            · have hnotfun : res.qualType.etyp.isFunctionType = false := by
                simp [hRef_res, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
              have hguard : qtypGuardDesc? res.qualType = none := by
                simp [qtypGuardDesc?, hpred_res]
              intro qt' k d hinq hqd
              exact
                QTypRespectsTagMeaning_of_nonFunction_noGuard tm res.qualType hnotfun hguard
                  hinq hqd
        | assign e1 e2 =>
            have hstruct := typecheckAssign_structure ctx e1 e2 fuel' res htc
            rcases hstruct with
              ⟨_result1, _result2, _ls, _htc1, _hRef, _htc2, _hInt, _hnextLoc, _hnextTag,
                _hregime, hetyp_res, _hpoison_res, hpred_res⟩
            have hmem_formula := typecheckAssign_memEnv_formula ctx e1 e2 fuel' res htc
            rcases hmem_formula with
              ⟨result1, result2, ls, htc1, _hRef, htc2, _hInt, hmem_res, _hRegime⟩
            have htc1' : typecheck .ioFree ctx e1 (fuel' - 1) = .ok result1 := by
              simpa [typecheck] using htc1
            have hTm1 := IH_wf (fuel' - 1) (by omega) tm ctx e1 result1 hwf htc1'
            have hresTm1 : QTypRespectsTagMeaning tm result1.qualType :=
              IH_qt (fuel' - 1) (by omega) tm ctx e1 result1 hwf htc1'
            have hwf_mid : wfTagMeaningCtx tm (updateCtxFromResult ctx result1) := by
              simpa [wfTagMeaningCtx, ctxAfter, updateCtxFromResult] using hTm1
            have htc2' : typecheck .ioFree (updateCtxFromResult ctx result1) e2 (fuel' - 1) = .ok result2 := by
              simpa [typecheck] using htc2
            have hTm2 := IH_wf (fuel' - 1) (by omega) tm (updateCtxFromResult ctx result1) e2 result2 hwf_mid htc2'
            have hresTm2 : QTypRespectsTagMeaning tm result2.qualType :=
              IH_qt (fuel' - 1) (by omega) tm (updateCtxFromResult ctx result1) e2 result2 hwf_mid htc2'
            refine ⟨?_, ?_⟩
            · let storedPred : Predicate :=
                if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred
              let storedQt : QTyp :=
                { etyp := ETyp.int
                  poison := joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison)
                  pred := storedPred }
              have hstored_pred_respects : PredRespectsTagMeaning tm storedPred := by
                intro k arg_name pred_body var_env hpred
                by_cases hwrite : result1.qualType.poison = true ∨ ctx.pc = true
                · simp [storedPred, hwrite] at hpred
                · have hpred_res2 :
                    result2.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env := by
                    simpa [storedPred, hwrite] using hpred
                  have hqd2 :
                      qtypGuardDesc? result2.qualType =
                        some (k, { argName := arg_name, body := pred_body, capEnv := var_env }) := by
                    simp [qtypGuardDesc?, hpred_res2]
                  exact hresTm2 (QTypInQTyp.self result2.qualType) hqd2
              have hstored_qtyp : QTypRespectsTagMeaning tm storedQt := by
                unfold storedQt
                exact
                  QTypRespectsTagMeaning_int_of_predRespects
                    tm
                    (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
                    storedPred
                    hstored_pred_respects
              have hEnvTm_res2 : EnvRespectsTagMeaning tm ctx.varEnv result2.memEnv' := by
                simpa [wfTagMeaningCtx, ctxAfter, updateCtxFromResult] using hTm2
              have hEnvTm_res : EnvRespectsTagMeaning tm ctx.varEnv res.memEnv' := by
                rw [hmem_res]
                cases hls : Std.ExtTreeSet.toList ls with
                | nil =>
                    simp
                    exact
                      EnvRespectsTagMeaning_updateLocsetWeak
                        tm ctx.varEnv result2.memEnv' ls
                        (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
                        storedPred
                        hEnvTm_res2
                        hstored_pred_respects
                | cons x xs =>
                    cases xs with
                    | nil =>
                        simp
                        exact
                          EnvRespectsTagMeaning_updateMemEnv
                            tm ctx.varEnv result2.memEnv' x storedQt (by simp [storedQt]) hEnvTm_res2 hstored_qtyp
                    | cons y ys =>
                        simp
                        exact
                          EnvRespectsTagMeaning_updateLocsetWeak
                            tm ctx.varEnv result2.memEnv' ls
                            (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
                            storedPred
                            hEnvTm_res2
                            hstored_pred_respects
              exact wfTagMeaningCtx_ctxAfter tm ctx res hEnvTm_res
            · have hnotfun : res.qualType.etyp.isFunctionType = false := by
                simp [hetyp_res, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
              have hguard : qtypGuardDesc? res.qualType = none := by
                simp [qtypGuardDesc?, hpred_res]
              intro qt' k d hinq hqd
              exact
                QTypRespectsTagMeaning_of_nonFunction_noGuard tm res.qualType hnotfun hguard
                  hinq hqd
        -- ===== Branch/join cases =====
        -- All ite modes produce noPred in result qualType.
        | ite e1 e2 e3 =>
            simp at htc
            have hstruct := typecheckIf_structure ctx e1 e2 e3 fuel' res htc
            cases hstruct with
            | inl h1 =>
                -- Mode 1: only true branch. res.qualType.etyp = res2.qualType.etyp, pred = noPred
                rcases h1 with ⟨k, deps, _, _, res1, _htc1, _hbool, res2, htc2, hmemEnv, _, _, _, _, _, hetyp_res⟩
                have htc2' : typecheck .ioFree { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ } e2 (fuel' - 1) = .ok res2 := by
                  simpa [typecheck] using htc2
                have hwf_true : wfTagMeaningCtx tm { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ } := by
                  simpa [wfTagMeaningCtx, ctxAfter] using hwf
                have hIH2_wf := IH_wf (fuel' - 1) (by omega) tm { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ } e2 res2 hwf_true htc2'
                have hIH2_qt : QTypRespectsTagMeaning tm res2.qualType :=
                  IH_qt (fuel' - 1) (by omega) tm { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ } e2 res2 hwf_true htc2'
                refine ⟨?_, ?_⟩
                · simpa [wfTagMeaningCtx, ctxAfter, hmemEnv] using hIH2_wf
                · exact QTypRespectsTagMeaning_of_etyp_noPred tm res2.qualType res.qualType
                    hIH2_qt hetyp_res (typecheckIf_pred_noPred ctx e1 e2 e3 fuel' res htc)
            | inr h_rest =>
              cases h_rest with
              | inl h2 =>
                  -- Mode 2: only false branch. res.qualType.etyp = res3.qualType.etyp, pred = noPred
                  rcases h2 with ⟨k, deps, _, _, res1, _htc1, _hbool, res3, htc3, hmemEnv, _, _, _, _, _, hetyp_res⟩
                  let ctxFalse := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩ }
                  have htc3' : typecheck .ioFree ctxFalse e3 (fuel' - 1) = .ok res3 := by
                    simpa [typecheck, ctxFalse] using htc3
                  have hwf_false : wfTagMeaningCtx tm ctxFalse := by
                    simpa [wfTagMeaningCtx, ctxAfter, ctxFalse] using hwf
                  have hIH3_wf := IH_wf (fuel' - 1) (by omega) tm ctxFalse e3 res3 hwf_false htc3'
                  have hIH3_qt : QTypRespectsTagMeaning tm res3.qualType :=
                    IH_qt (fuel' - 1) (by omega) tm ctxFalse e3 res3 hwf_false htc3'
                  refine ⟨?_, ?_⟩
                  · simpa [wfTagMeaningCtx, ctxAfter, hmemEnv, ctxFalse] using hIH3_wf
                  · exact QTypRespectsTagMeaning_of_etyp_noPred tm res3.qualType res.qualType
                      hIH3_qt hetyp_res (typecheckIf_pred_noPred ctx e1 e2 e3 fuel' res htc)
              | inr h_rest2 =>
                cases h_rest2 with
                | inl h3 =>
                    -- Mode 3: both branches, join. res.qualType.pred = noPred.
                    rcases h3 with ⟨k, deps, _, _, res1, _htc1, _hbool, res2, htc2, res3, htc3_raw, hmemEnv, _, _, _, _, _hpoison, hetyp_res, hpred_res⟩
                    let branchPc := joinPoison ctx.pc res1.qualType.poison
                    let ctxTrue := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩, pc := branchPc }
                    have htc2' : typecheck .ioFree ctxTrue e2 (fuel' - 1) = .ok res2 := by
                      simpa [typecheck, ctxTrue, branchPc] using htc2
                    have hwf_true : wfTagMeaningCtx tm ctxTrue := by
                      simpa [wfTagMeaningCtx, ctxAfter, ctxTrue] using hwf
                    have hIH2 := IH_wf (fuel' - 1) (by omega) tm ctxTrue e2 res2 hwf_true htc2'
                    have hIH2_qt : QTypRespectsTagMeaning tm res2.qualType :=
                      IH_qt (fuel' - 1) (by omega) tm ctxTrue e2 res2 hwf_true htc2'
                    -- For mode 3 false branch QTypRespects
                    let ctxFalse := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩, pc := branchPc }
                    have htc3' : typecheck .ioFree { ctxFalse with nextLoc := res2.nextLoc', nextTag := res2.nextTag' } e3 (fuel' - 1) = .ok res3 := by
                      simpa [typecheck, ctxFalse, branchPc] using htc3_raw
                    have hwf_false : wfTagMeaningCtx tm { ctxFalse with nextLoc := res2.nextLoc', nextTag := res2.nextTag' } := by
                      simpa [wfTagMeaningCtx, ctxAfter, ctxFalse] using hwf
                    have hIH3_qt : QTypRespectsTagMeaning tm res3.qualType :=
                      IH_qt (fuel' - 1) (by omega) tm { ctxFalse with nextLoc := res2.nextLoc', nextTag := res2.nextTag' } e3 res3 hwf_false htc3'
                    have hIH2' : EnvRespectsTagMeaning tm ctx.varEnv res2.memEnv' := by
                      simpa [wfTagMeaningCtx, ctxAfter, ctxTrue] using hIH2
                    refine ⟨?_, ?_⟩
                    · simp only [wfTagMeaningCtx, ctxAfter]
                      rw [hmemEnv]
                      exact EnvRespectsTagMeaning_joinMemEnvsStrong' tm ctx.varEnv res2.memEnv' res3.memEnv' hIH2'
                    · -- Use joinStep + etyp_noPred transport.
                      -- @[reducible] QTypRespectsTagMeaning requires intro + full application.
                      cases hq2 : res2.qualType with
                      | mk e2 p2 pred2 =>
                      cases hq3 : res3.qualType with
                      | mk e3' p3 pred3 =>
                      have hjoin_qt : QTypRespectsTagMeaning tm
                          ⟨joinETyps e2 e3' p2 p3, joinPoison p2 p3, joinPredicates pred2 pred3⟩ :=
                        QTypRespectsTagMeaning_joinStep tm e2 e3' p2 p3 pred2 pred3
                          (hq2 ▸ hIH2_qt) (hq3 ▸ hIH3_qt)
                      simp only [hq2, hq3] at hetyp_res
                      intro q' k' d' hinq hgd
                      exact QTypRespectsTagMeaning_of_etyp_noPred tm
                        ⟨joinETyps e2 e3' p2 p3, joinPoison p2 p3, joinPredicates pred2 pred3⟩
                        res.qualType hjoin_qt hetyp_res hpred_res hinq hgd
                | inr h4 =>
                    -- Mode 4: matchGuard fails, both branches, join. res.qualType.pred = noPred.
                    obtain ⟨⟨err, _hmatch_fail⟩, res1, htc1, _hbool, res2, htc2, res3, htc3_raw, hmemEnv, _, _, _, _, _hpoison, hetyp_res, hpred_res⟩ := h4
                    let ctx1 : TypeContext := { ctx with memEnv := res1.memEnv', tagEnv := res1.tagEnv',
                                                         nextLoc := res1.nextLoc', nextTag := res1.nextTag', regime := res1.regime' }
                    let pc' := joinPoison ctx.pc res1.qualType.poison
                    let ctx'' := { ctx1 with pc := pc' }
                    have htc1' : typecheck .ioFree ctx e1 (fuel' - 1) = .ok res1 := by simpa [typecheck] using htc1
                    have hIH1 := IH_wf (fuel' - 1) (by omega) tm ctx e1 res1 hwf htc1'
                    have hwf_mid : wfTagMeaningCtx tm ctx'' := by
                      simp only [wfTagMeaningCtx, ctx'', ctx1]
                      simpa [wfTagMeaningCtx, ctxAfter] using hIH1
                    have htc2' : typecheck .ioFree ctx'' e2 (fuel' - 1) = .ok res2 := by
                      simpa [typecheck, ctx'', ctx1, pc'] using htc2
                    have hIH2 := IH_wf (fuel' - 1) (by omega) tm ctx'' e2 res2 hwf_mid htc2'
                    have hIH2_qt : QTypRespectsTagMeaning tm res2.qualType :=
                      IH_qt (fuel' - 1) (by omega) tm ctx'' e2 res2 hwf_mid htc2'
                    -- For mode 4 false branch QTypRespects
                    let ctx''3 := { ctx'' with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
                    have htc3' : typecheck .ioFree ctx''3 e3 (fuel' - 1) = .ok res3 := by
                      simpa [typecheck, ctx''3, ctx'', ctx1, pc'] using htc3_raw
                    have hwf_mid3 : wfTagMeaningCtx tm ctx''3 := by
                      simpa [wfTagMeaningCtx, ctxAfter, ctx''3, ctx'', ctx1] using hwf_mid
                    have hIH3_qt : QTypRespectsTagMeaning tm res3.qualType :=
                      IH_qt (fuel' - 1) (by omega) tm ctx''3 e3 res3 hwf_mid3 htc3'
                    have hIH2' : EnvRespectsTagMeaning tm ctx.varEnv res2.memEnv' := by
                      simpa [wfTagMeaningCtx, ctxAfter, ctx'', ctx1] using hIH2
                    refine ⟨?_, ?_⟩
                    · simp only [wfTagMeaningCtx, ctxAfter]
                      rw [hmemEnv]
                      exact EnvRespectsTagMeaning_joinMemEnvsStrong' tm ctx.varEnv res2.memEnv' res3.memEnv' hIH2'
                    · -- @[reducible] QTypRespectsTagMeaning requires intro + full application.
                      cases hq2 : res2.qualType with
                      | mk e2' p2 pred2 =>
                      cases hq3 : res3.qualType with
                      | mk e3' p3 pred3 =>
                      have hjoin_qt : QTypRespectsTagMeaning tm
                          ⟨joinETyps e2' e3' p2 p3, joinPoison p2 p3, joinPredicates pred2 pred3⟩ :=
                        QTypRespectsTagMeaning_joinStep tm e2' e3' p2 p3 pred2 pred3
                          (hq2 ▸ hIH2_qt) (hq3 ▸ hIH3_qt)
                      simp only [hq2, hq3] at hetyp_res
                      intro q' k' d' hinq hgd
                      exact QTypRespectsTagMeaning_of_etyp_noPred tm
                        ⟨joinETyps e2' e3' p2 p3, joinPoison p2 p3, joinPredicates pred2 pred3⟩
                        res.qualType hjoin_qt hetyp_res hpred_res hinq hgd
        -- notExpr is not a constructor of Expr; it desugars during parsing
        -- ===== App and kwhile cases =====
        | app e1 e2 =>
            cases fuel' with
            | zero =>
                simp [typecheckApp] at htc
            | succ fuel'' =>
                have htcApp : typecheckApp .ioFree ctx e1 e2 (Nat.succ fuel'') = .ok res := htc
                obtain ⟨result2, result1, etyp2, p2, pred2, hqt2, htc2, htc1, h_arrow_or_parrow⟩ :=
                  typecheckApp_arrow_structure_full ctx e1 e2 fuel'' res htcApp
                have htc2' : typecheck .ioFree ctx e2 fuel'' = .ok result2 := by
                  simpa [typecheck] using htc2
                have hIH2_wf := IH_wf fuel'' (by omega) tm ctx e2 result2 hwf htc2'
                have hIH2_qt : QTypRespectsTagMeaning tm result2.qualType :=
                  IH_qt fuel'' (by omega) tm ctx e2 result2 hwf htc2'
                have hTm2 : wfTagMeaningCtx tm (ctxAfter ctx result2) := by
                  simpa [ctxAfter] using hIH2_wf
                have htc1' : typecheck .ioFree (ctxAfter ctx result2) e1 fuel'' = .ok result1 := by
                  simp [ctxAfter] at htc1 ⊢
                  exact htc1
                have hIH1_wf := IH_wf fuel'' (by omega) tm (ctxAfter ctx result2) e1 result1 hTm2 htc1'
                have hIH1_qt : QTypRespectsTagMeaning tm result1.qualType :=
                  IH_qt fuel'' (by omega) tm (ctxAfter ctx result2) e1 result1 hTm2 htc1'
                cases h_arrow_or_parrow with
                | inl h_arrow =>
                    obtain ⟨st1, st2, p, p1, tcls, results, first, rest, hetyp1, _hp1, _hnpure,
                      _hnempty, _hsub, hmap, heq_results, h_join⟩ := h_arrow
                    have hTm1_ctx : wfTagMeaningCtx tm (ctxAfter ctx result1) := by
                      simpa [ctxAfter] using hIH1_wf
                    have hresTm2_arg : QTypRespectsTagMeaning tm ⟨etyp2, p2, pred2⟩ := by
                      rw [← hqt2]
                      exact hIH2_qt
                    have hresults_tm :
                        ∀ r, r ∈ results → wfTagMeaningCtx tm (ctxAfter ctx r) :=
                      mapM_applyFnTClosure_forall_wfTagMeaningCtx_byIH
                        (tm := tm)
                        (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                        (tcls := tcls)
                        (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                        (result1 := result1) (fuel := fuel'')
                        (results := results)
                        (bodyIH := fun m hm ctx e res hwf htc =>
                          IH_wf m (by omega) tm ctx e res hwf htc)
                        hTm1_ctx hIH1_qt hetyp1 hresTm2_arg hmap
                    have hresults_qtm :
                        ∀ r, r ∈ results → QTypRespectsTagMeaning tm r.qualType :=
                      mapM_applyFnTClosure_forall_QTypRespectsTagMeaning_byIH
                        (tm := tm)
                        (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                        (tcls := tcls)
                        (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                        (result1 := result1) (fuel := fuel'')
                        (results := results)
                        (bodyIH := fun m hm ctx e res hwf htc =>
                          IH_qt m (by omega) tm ctx e res hwf htc)
                        hTm1_ctx hIH1_qt hetyp1 hresTm2_arg hmap
                    have hfirst_in_results : first ∈ results := by
                      simp [heq_results]
                    have h_first_tm : wfTagMeaningCtx tm (ctxAfter ctx first) :=
                      hresults_tm first hfirst_in_results
                    have h_first_qtm : QTypRespectsTagMeaning tm first.qualType := by
                      intro qt' k d hinq hqd
                      exact hresults_qtm first hfirst_in_results hinq hqd
                    have h_rest_qtm : ∀ r ∈ rest, QTypRespectsTagMeaning tm r.qualType := by
                      intro r hr
                      have hmem_results : r ∈ results := by
                        have : r ∈ first :: rest := by simp [hr]
                        simpa [heq_results] using this
                      intro qt' k d hinq hqd
                      exact hresults_qtm r hmem_results hinq hqd
                    exact
                      ⟨ join_transport_wfTagMeaningCtx_byFirst tm ctx first rest res h_join h_first_tm
                      , joinTypeResults_QTypRespectsTagMeaning_byMembers tm ctx first rest res
                          h_join h_first_qtm h_rest_qtm ⟩
                | inr h_parrow =>
                    obtain ⟨st1, st2, p, p1, tcls, results, first, rest, hetyp1, _hp1,
                      _hnempty, _hsub, hmap, heq_results, h_join⟩ := h_parrow
                    have hTm1_ctx : wfTagMeaningCtx tm (ctxAfter ctx result1) := by
                      simpa [ctxAfter] using hIH1_wf
                    have hresTm2_arg : QTypRespectsTagMeaning tm ⟨etyp2, p2, pred2⟩ := by
                      rw [← hqt2]
                      exact hIH2_qt
                    have hresults_tm :
                        ∀ r, r ∈ results → wfTagMeaningCtx tm (ctxAfter ctx r) :=
                      mapM_applyPFnTClosure_forall_wfTagMeaningCtx_byIH
                        (tm := tm)
                        (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                        (tcls := tcls)
                        (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                        (result1 := result1) (fuel := fuel'')
                        (results := results)
                        (bodyIH := fun m hm ctx e res hwf htc =>
                          IH_wf m (by omega) tm ctx e res hwf htc)
                        hTm1_ctx hIH1_qt hetyp1 hresTm2_arg hmap
                    have hresults_qtm :
                        ∀ r, r ∈ results → QTypRespectsTagMeaning tm r.qualType :=
                      mapM_applyPFnTClosure_forall_QTypRespectsTagMeaning_byIH
                        (tm := tm)
                        (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                        (tcls := tcls)
                        (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                        (result1 := result1) (fuel := fuel'')
                        (results := results)
                        (bodyIH := fun m hm ctx e res hwf htc =>
                          IH_qt m (by omega) tm ctx e res hwf htc)
                        hTm1_ctx hIH1_qt hetyp1 hresTm2_arg hmap
                    have hfirst_in_results : first ∈ results := by
                      simp [heq_results]
                    have h_first_tm : wfTagMeaningCtx tm (ctxAfter ctx first) :=
                      hresults_tm first hfirst_in_results
                    have h_first_qtm : QTypRespectsTagMeaning tm first.qualType := by
                      intro qt' k d hinq hqd
                      exact hresults_qtm first hfirst_in_results hinq hqd
                    have h_rest_qtm : ∀ r ∈ rest, QTypRespectsTagMeaning tm r.qualType := by
                      intro r hr
                      have hmem_results : r ∈ results := by
                        have : r ∈ first :: rest := by simp [hr]
                        simpa [heq_results] using this
                      intro qt' k d hinq hqd
                      exact hresults_qtm r hmem_results hinq hqd
                    exact
                      ⟨ join_transport_wfTagMeaningCtx_byFirst tm ctx first rest res h_join h_first_tm
                      , joinTypeResults_QTypRespectsTagMeaning_byMembers tm ctx first rest res
                          h_join h_first_qtm h_rest_qtm ⟩
        | kwhile e1 e2 =>
            sorry -- permanently postponed: kwhile proofs are out of active scope

lemma typecheckExpr_preserves_wfTagMeaningCtx
    (tm : TagMeaning) (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (hwf : wfTagMeaningCtx tm ctx)
    (htc : typecheck .ioFree ctx e fuel = .ok res) :
    wfTagMeaningCtx tm (ctxAfter ctx res) :=
  (typecheckExpr_preserves_wfTagMeaningCtx_main fuel tm ctx e res hwf htc).1

lemma typecheckExpr_preserves_QTypRespectsTagMeaning
    (tm : TagMeaning) (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (hwf : wfTagMeaningCtx tm ctx)
    (htc : typecheck .ioFree ctx e fuel = .ok res) :
    QTypRespectsTagMeaning tm res.qualType :=
  (typecheckExpr_preserves_wfTagMeaningCtx_main fuel tm ctx e res hwf htc).2

lemma typecheckExpr_QTypRespectsTagMeaning_of_ok
    (tm : TagMeaning) (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (hwf : wfTagMeaningCtx tm ctx)
    (htc : typecheck .ioFree ctx e fuel = .ok res) :
    QTypRespectsTagMeaning tm res.qualType :=
  typecheckExpr_preserves_QTypRespectsTagMeaning tm ctx e fuel res hwf htc

-- ═══════════════════════════════════════════════════════════════════════════
-- Shared clean-lookup infrastructure (moved from StepFRApp.lean)
-- These helpers support typecheckExpr_clean_lookup_origin_of_pc_true and
-- typecheckExpr_lookup_clean_back_of_pc_true, used by multiple StepFR* files.
-- ═══════════════════════════════════════════════════════════════════════════

lemma applyPFnTClosure_regular_inv
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuelBody : Nat)
  (x : Name) (pbody : PExpr) (tenv : CapturedVarEnv)
  (first : TypeResult)
  (happly :
    applyPFnTClosure .ioFree (PFnTClosure.regular x pbody tenv) st1 st2 p p1
      argEtyp argPoison argPred ctx result2 (Nat.succ fuelBody) = .ok first) :
  ∃ result3,
    typecheckExpr .ioFree
      { ctx with
        pc := joinPoison p (joinPoison ctx.pc p1)
        memEnv := result2.memEnv'
        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
          ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        tagEnv := result2.tagEnv'
        pureCtx := true
        nextTag := result2.nextTag'
        nextLoc := result2.nextLoc'
        regime := result2.regime' } (PExpr.toExpr pbody) fuelBody = .ok result3 ∧
    isSubtype st2 result3.qualType = true ∧
    first =
      { result3 with
        qualType :=
          normalizeAppResultByProvenance (joinPoison p1 p)
            { result3.qualType with poison := joinPoison p1 (joinPoison p result3.qualType.poison) } } := by
  unfold applyPFnTClosure at happly
  simp [bind, Except.bind] at happly
  cases htc_body : typecheckExpr .ioFree
      { ctx with
        pc := joinPoison p (joinPoison ctx.pc p1)
        memEnv := result2.memEnv'
        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
          ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        tagEnv := result2.tagEnv'
        pureCtx := true
        nextTag := result2.nextTag'
        nextLoc := result2.nextLoc'
        regime := result2.regime' } (PExpr.toExpr pbody) fuelBody with
  | error err =>
      simp [htc_body] at happly
  | ok result3 =>
      simp [htc_body] at happly
      cases hsub : isSubtype st2 result3.qualType with
      | false =>
          cases hq3 : result3.qualType with
          | mk et3 p3 pred3 =>
              have hsub' : isSubtype st2 { etyp := et3, poison := p3, pred := pred3 } = false := by
                simpa [hq3] using hsub
              simp [hq3, hsub'] at happly
      | true =>
          cases hq3 : result3.qualType with
          | mk et3 p3 pred3 =>
              have hsub' : isSubtype st2 { etyp := et3, poison := p3, pred := pred3 } = true := by
                simpa [hq3] using hsub
              have happly' :
                  (Except.ok first : Except String TypeResult) =
                    Except.ok
                      { result3 with
                        qualType :=
                          normalizeAppResultByProvenance (joinPoison p1 p)
                            { result3.qualType with
                              poison := joinPoison p1 (joinPoison p result3.qualType.poison) } } := by
                simpa [hq3, hsub', pure, Except.pure] using happly.symm
              have hfirst :
                  first =
                    { result3 with
                      qualType :=
                        normalizeAppResultByProvenance (joinPoison p1 p)
                          { result3.qualType with
                            poison := joinPoison p1 (joinPoison p result3.qualType.poison) } } := by
                injection happly' with hEq
              exact ⟨result3, rfl, hsub, hfirst⟩

lemma applyPFnTClosure_ioFree_extern_fails
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuel : Nat)
  (x : Name) (retSpec : ExternReturn) (capturedEnv : CapturedVarEnv)
  (r : TypeResult) :
  applyPFnTClosure .ioFree (PFnTClosure.extern x retSpec capturedEnv) st1 st2 p p1
    argEtyp argPoison argPred ctx result2 fuel ≠ .ok r := by
  intro h
  cases fuel with
  | zero =>
    unfold applyPFnTClosure at h
    simp at h
  | succ _ =>
    unfold applyPFnTClosure at h
    have hcond : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := rfl
    simp only [hcond, ite_true, bind, Except.bind] at h
    exact absurd h (Except.error_ne_ok "Extern function application forbidden in ioFree mode" r)

lemma cleanUnder_of_monotone {R R' : Regime} {qt : QTyp} :
    Regime.monotoneStep R R' → qtypCleanUnder R' qt → qtypCleanUnder R qt := by
  intro h_mono h_clean
  cases h_clean with
  | clean hpoison =>
      exact qtypCleanUnder.clean hpoison
  | guard k htag hkR' hnotfun =>
      have hRdef : R.lookup? k ≠ none := h_mono.2.2 k (by simp [hkR'])
      cases hkR : R.lookup? k with
      | none => exact (hRdef hkR).elim
      | some b =>
          have h_cases := h_mono.2.1 k b hkR
          cases h_cases with
          | inl hkR'_preserved =>
              have hb : b = true := by
                have : some b = some true := hkR'_preserved.symm.trans hkR'
                exact Option.some.inj this
              subst hb
              exact qtypCleanUnder.guard k htag hkR hnotfun
          | inr hkR'_none =>
              simp [hkR'_none] at hkR'

lemma joinTypeResults_lookup_head_guardTag_compat
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (l : Loc) (qt qt_first : QTyp) (k : Tag)
  (hlookup_res : (ctxAfter ctx res).memEnv.lookup l = some qt)
  (hlookup_first : (ctxAfter ctx first).memEnv.lookup l = some qt_first)
  (htag_res : qtypGuardTag qt = some k) :
  qtypGuardTag qt_first = some k := by
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
        TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvsStrong acc.2.1 result.memEnv',
              joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred,
              joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 result.regime',
              max acc.2.2.2.2.2.2.1 result.nextLoc',
              max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_guardTag :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
        (qt_acc : QTyp),
        List.foldlM joinStep acc rs' = .ok acc' →
        acc.2.1.lookup l = some qt_acc →
        acc'.2.1.lookup l = some qt →
        qtypGuardTag qt = some k →
        qtypGuardTag qt_acc = some k := by
    intro rs' acc acc' qt_acc hfold hlookup_acc hlookup_out htag_out
    induction rs' generalizing acc qt_acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        have hqeq : qt_acc = qt := by
          have hqeq_opt : some qt_acc = some qt := by
            calc
              some qt_acc = acc.2.1.lookup l := hlookup_acc.symm
              _ = some qt := hlookup_out
          exact Option.some.inj hqeq_opt
        subst hqeq
        exact htag_out
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv',
                joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred,
                joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc',
                max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            obtain ⟨qt_mid, hlookup_mid⟩ :=
              joinMemEnvsStrong_lookup_some_of_left_lookup
                (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt1 := qt_acc) hlookup_acc
            have htag_mid : qtypGuardTag qt_mid = some k :=
              ih (acc := acc1) (qt_acc := qt_mid) hfold_tail hlookup_mid
            exact
              joinMemEnvsStrong_lookup_guardTag_left
                (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt := qt_mid) (qt1 := qt_acc) (k := k)
                hlookup_mid hlookup_acc htag_mid
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at _h_join
      cases hcheck :
          (List.foldlM
            (fun x result =>
              match result.qualType with
              | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                if beqETypSignature etyp resEtyp = false then
                  Except.error
                    (toString "Closure alternatives produced incompatible result types: " ++
                      toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
                else Except.ok ())
            () rest : Except String Unit) with
      | error err =>
          erw [hcheck] at _h_join
          simp at _h_join
      | ok _ =>
          erw [hcheck] at _h_join
          simp at _h_join
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                  first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              have hlookup_first' : first.memEnv'.lookup l = some qt_first := by
                simpa [ctxAfter] using hlookup_first
              have hlookup_res' : a.2.1.lookup l = some qt := by
                simpa [ctxAfter] using hlookup_res
              exact
                h_fold_guardTag
                  rest
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                    first.nextTag')
                  a qt_first
                  hfold hlookup_first' hlookup_res' htag_res


lemma joinTypeResults_lookup_head_regime_compat
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (k : Tag) (b : Bool)
  (hlookup_res : (ctxAfter ctx res).regime.lookup? k = some b) :
  (ctxAfter ctx first).regime.lookup? k = some b := by
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
        TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvsStrong acc.2.1 result.memEnv',
              joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred,
              joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 result.regime',
              max acc.2.2.2.2.2.2.1 result.nextLoc',
              max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_regime :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        acc'.2.2.2.2.2.1.lookup? k = some b →
        acc.2.2.2.2.2.1.lookup? k = some b := by
    intro rs' acc acc' hfold hlookup_out
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        exact hlookup_out
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv',
                joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred,
                joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc',
                max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have hlookup_mid : acc1.2.2.2.2.2.1.lookup? k = some b :=
              ih (acc := acc1) hfold_tail
            exact
              joinRegimes_lookup_some_left
                (R1 := acc.2.2.2.2.2.1) (R2 := x.regime') (k := k) (b := b) hlookup_mid
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at _h_join
      cases hcheck :
          (List.foldlM
            (fun x result =>
              match result.qualType with
              | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                if beqETypSignature etyp resEtyp = false then
                  Except.error
                    (toString "Closure alternatives produced incompatible result types: " ++
                      toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
                else Except.ok ())
            () rest : Except String Unit) with
      | error err =>
          erw [hcheck] at _h_join
          simp at _h_join
      | ok _ =>
          erw [hcheck] at _h_join
          simp at _h_join
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                  first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              exact
                h_fold_regime
                  rest
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                    first.nextTag')
                  a
                  hfold (by simpa [ctxAfter] using hlookup_res)


lemma joinTypeResults_lookup_head_poison_imp
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (l : Loc) (qt qt_first : QTyp)
  (hlookup_res : (ctxAfter ctx res).memEnv.lookup l = some qt)
  (hlookup_first : (ctxAfter ctx first).memEnv.lookup l = some qt_first) :
  qt.poison = false → qt_first.poison = false := by
  intro hpoison_res
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
        TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvsStrong acc.2.1 result.memEnv',
              joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred,
              joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 result.regime',
              max acc.2.2.2.2.2.2.1 result.nextLoc',
              max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_poison :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
        (qt_acc : QTyp),
        List.foldlM joinStep acc rs' = .ok acc' →
        acc.2.1.lookup l = some qt_acc →
        acc'.2.1.lookup l = some qt →
        qt.poison = false →
        qt_acc.poison = false := by
    intro rs' acc acc' qt_acc hfold hlookup_acc hlookup_out hclean_out
    induction rs' generalizing acc qt_acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        have hqeq : qt_acc = qt := by
          have hqeq_opt : some qt_acc = some qt := by
            calc
              some qt_acc = acc.2.1.lookup l := hlookup_acc.symm
              _ = some qt := hlookup_out
          exact Option.some.inj hqeq_opt
        subst hqeq
        exact hclean_out
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv',
                joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred,
                joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc',
                max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            obtain ⟨qt_mid, hlookup_mid⟩ :=
              joinMemEnvsStrong_lookup_some_of_left_lookup
                (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt1 := qt_acc) hlookup_acc
            have hclean_mid : qt_mid.poison = false :=
              ih (acc := acc1) (qt_acc := qt_mid) hfold_tail hlookup_mid
            have hacc_not_none : acc.2.1.lookup l ≠ none := by
              intro hnone
              rw [hlookup_acc] at hnone
              cases hnone
            have hleft_clean :=
              joinMemEnvsStrong_lookup_clean_left
                (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt := qt_mid)
                hlookup_mid hclean_mid hacc_not_none
            rcases hleft_clean with ⟨qt_acc', hlookup_acc', _hetyp, hpoison_acc'⟩
            have hqeq : qt_acc' = qt_acc := by
              have hqeq_opt : some qt_acc' = some qt_acc := by
                calc
                  some qt_acc' = acc.2.1.lookup l := hlookup_acc'.symm
                  _ = some qt_acc := hlookup_acc
              exact Option.some.inj hqeq_opt
            subst hqeq
            exact hpoison_acc'
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at _h_join
      cases hcheck :
          (List.foldlM
            (fun x result =>
              match result.qualType with
              | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                if beqETypSignature etyp resEtyp = false then
                  Except.error
                    (toString "Closure alternatives produced incompatible result types: " ++
                      toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
                else Except.ok ())
            () rest : Except String Unit) with
      | error err =>
          erw [hcheck] at _h_join
          simp at _h_join
      | ok _ =>
          erw [hcheck] at _h_join
          simp at _h_join
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                  first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              have hlookup_first' : first.memEnv'.lookup l = some qt_first := by
                simpa [ctxAfter] using hlookup_first
              have hlookup_res' : a.2.1.lookup l = some qt := by
                simpa [ctxAfter] using hlookup_res
              exact
                h_fold_poison
                  rest
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                    first.nextTag')
                  a qt_first
                  hfold hlookup_first' hlookup_res' hpoison_res


lemma joinTypeResults_lookup_member_regime_compat
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (k : Tag) (b : Bool)
  (hlookup_res : (ctxAfter ctx res).regime.lookup? k = some b) :
  (ctxAfter ctx src).regime.lookup? k = some b := by
  rcases (List.mem_cons.mp _hmem_src) with hsrc | hsrc_rest
  · subst src
    simpa using
      (joinTypeResults_lookup_head_regime_compat
        (ctx := ctx) (first := first) (rest := rest) (res := res)
        _h_join k b hlookup_res)
  · let joinStep :
        (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
          TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
      fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
        match result.qualType with
        | ⟨resEtyp, resPoison, resPred⟩ =>
            Except.ok
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 result.memEnv',
                joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred,
                joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 result.regime',
                max acc.2.2.2.2.2.2.1 result.nextLoc',
                max acc.2.2.2.2.2.2.2 result.nextTag')
    have h_fold_regime_members :
        ∀ (rs' : List TypeResult)
          (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
          List.foldlM joinStep acc rs' = .ok acc' →
          acc'.2.2.2.2.2.1.lookup? k = some b →
          (acc.2.2.2.2.2.1.lookup? k = some b) ∧
            (∀ r ∈ rs', r.regime'.lookup? k = some b) := by
      intro rs' acc acc' hfold hlookup_out
      induction rs' generalizing acc acc' with
      | nil =>
          simp [List.foldlM_nil, pure, Except.pure] at hfold
          subst acc'
          exact ⟨hlookup_out, by intro r hr; cases hr⟩
      | cons x xs ih =>
          cases hqx : x.qualType with
          | mk resEtyp resPoison resPred =>
              simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
              let acc1 :
                  ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
                (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                  joinMemEnvsStrong acc.2.1 x.memEnv',
                  joinPoison acc.2.2.1 resPoison,
                  joinPredicates acc.2.2.2.1 resPred,
                  joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                  joinRegimes acc.2.2.2.2.2.1 x.regime',
                  max acc.2.2.2.2.2.2.1 x.nextLoc',
                  max acc.2.2.2.2.2.2.2 x.nextTag')
              have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
                simpa [acc1] using hfold
              have htail_pack :=
                ih (acc := acc1) (acc' := acc') hfold_tail hlookup_out
              have hlookup_acc1 : acc1.2.2.2.2.2.1.lookup? k = some b := htail_pack.1
              have hlookup_acc : acc.2.2.2.2.2.1.lookup? k = some b :=
                joinRegimes_lookup_some_left
                  (R1 := acc.2.2.2.2.2.1) (R2 := x.regime') (k := k) (b := b) hlookup_acc1
              have hlookup_x : x.regime'.lookup? k = some b :=
                joinRegimes_lookup_some_right
                  (R1 := acc.2.2.2.2.2.1) (R2 := x.regime') (k := k) (b := b) hlookup_acc1
              refine ⟨hlookup_acc, ?_⟩
              intro r hr
              rcases (List.mem_cons.mp hr) with hrx | hrxs
              · subst r
                exact hlookup_x
              · exact htail_pack.2 r hrxs
    cases hqt : first.qualType with
    | mk etyp poison pred =>
        simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
          MonadExceptOf.throw, TypecheckM] at _h_join
        cases hcheck :
            (List.foldlM
              (fun x result =>
                match result.qualType with
                | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                  if beqETypSignature etyp resEtyp = false then
                    Except.error
                      (toString "Closure alternatives produced incompatible result types: " ++
                        toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
                  else Except.ok ())
              () rest : Except String Unit) with
        | error err =>
            erw [hcheck] at _h_join
            simp at _h_join
        | ok _ =>
            erw [hcheck] at _h_join
            simp at _h_join
            cases hfold :
                List.foldlM joinStep
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                    first.nextTag') rest with
            | error err =>
                erw [hfold] at _h_join
                simp at _h_join
            | ok a =>
                erw [hfold] at _h_join
                simp at _h_join
                subst res
                have hlookup_res' : a.2.2.2.2.2.1.lookup? k = some b := by
                  simpa [ctxAfter] using hlookup_res
                have hpack :=
                  h_fold_regime_members
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a
                    hfold hlookup_res'
                have hsrc_lookup : src.regime'.lookup? k = some b := hpack.2 src hsrc_rest
                simpa [ctxAfter] using hsrc_lookup


lemma joinTypeResults_lookup_member_guardTag_compat
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (l : Loc) (qt qt_src : QTyp) (k : Tag)
  (hlookup_res : (ctxAfter ctx res).memEnv.lookup l = some qt)
  (hlookup_src : (ctxAfter ctx src).memEnv.lookup l = some qt_src)
  (htag_res : qtypGuardTag qt = some k) :
  qtypGuardTag qt_src = some k := by
  rcases (List.mem_cons.mp _hmem_src) with hsrc | hsrc_rest
  · subst src
    simpa using
      (joinTypeResults_lookup_head_guardTag_compat
        (ctx := ctx) (first := first) (rest := rest) (res := res)
        _h_join l qt qt_src k hlookup_res hlookup_src htag_res)
  · let joinStep :
        (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
          TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
      fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
        match result.qualType with
        | ⟨resEtyp, resPoison, resPred⟩ =>
            Except.ok
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 result.memEnv',
                joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred,
                joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 result.regime',
                max acc.2.2.2.2.2.2.1 result.nextLoc',
                max acc.2.2.2.2.2.2.2 result.nextTag')
    have h_fold_guardTag :
        ∀ (rs' : List TypeResult)
          (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
          (qt_acc : QTyp),
          List.foldlM joinStep acc rs' = .ok acc' →
          acc.2.1.lookup l = some qt_acc →
          acc'.2.1.lookup l = some qt →
          qtypGuardTag qt = some k →
          qtypGuardTag qt_acc = some k := by
      intro rs' acc acc' qt_acc hfold hlookup_acc hlookup_out htag_out
      induction rs' generalizing acc acc' qt_acc with
      | nil =>
          simp [List.foldlM_nil, pure, Except.pure] at hfold
          subst acc'
          have hqeq : qt_acc = qt := by
            have hqeq_opt : some qt_acc = some qt := by
              calc
                some qt_acc = acc.2.1.lookup l := hlookup_acc.symm
                _ = some qt := hlookup_out
            exact Option.some.inj hqeq_opt
          subst hqeq
          exact htag_out
      | cons x xs ih =>
          cases hqx : x.qualType with
          | mk resEtyp resPoison resPred =>
              simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
              let acc1 :
                  ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
                (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                  joinMemEnvsStrong acc.2.1 x.memEnv',
                  joinPoison acc.2.2.1 resPoison,
                  joinPredicates acc.2.2.2.1 resPred,
                  joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                  joinRegimes acc.2.2.2.2.2.1 x.regime',
                  max acc.2.2.2.2.2.2.1 x.nextLoc',
                  max acc.2.2.2.2.2.2.2 x.nextTag')
              have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
                simpa [acc1] using hfold
              obtain ⟨qt_mid, hlookup_mid⟩ :=
                joinMemEnvsStrong_lookup_some_of_left_lookup
                  (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt1 := qt_acc) hlookup_acc
              have htag_mid : qtypGuardTag qt_mid = some k :=
                ih (acc := acc1) (acc' := acc') (qt_acc := qt_mid) hfold_tail hlookup_mid hlookup_out
              exact
                joinMemEnvsStrong_lookup_guardTag_left
                  (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt := qt_mid) (qt1 := qt_acc) (k := k)
                  hlookup_mid hlookup_acc htag_mid
    have h_fold_member_guardTag :
        ∀ (rs' : List TypeResult)
          (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
          (src' : TypeResult) (qt_src' : QTyp),
          List.foldlM joinStep acc rs' = .ok acc' →
          src' ∈ rs' →
          acc'.2.1.lookup l = some qt →
          qtypGuardTag qt = some k →
          src'.memEnv'.lookup l = some qt_src' →
          qtypGuardTag qt_src' = some k := by
      intro rs' acc acc' src' qt_src' hfold hmem_src' hlookup_out htag_out hlookup_src'
      induction rs' generalizing acc acc' src' qt_src' with
      | nil =>
          cases hmem_src'
      | cons x xs ih =>
          cases hqx : x.qualType with
          | mk resEtyp resPoison resPred =>
              simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
              let acc1 :
                  ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
                (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                  joinMemEnvsStrong acc.2.1 x.memEnv',
                  joinPoison acc.2.2.1 resPoison,
                  joinPredicates acc.2.2.2.1 resPred,
                  joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                  joinRegimes acc.2.2.2.2.2.1 x.regime',
                  max acc.2.2.2.2.2.2.1 x.nextLoc',
                  max acc.2.2.2.2.2.2.2 x.nextTag')
              have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
                simpa [acc1] using hfold
              rcases (List.mem_cons.mp hmem_src') with hsrc_eq | hsrc_tail
              · subst src'
                have hlookup_acc1_exists :
                    ∃ qt_acc1, acc1.2.1.lookup l = some qt_acc1 := by
                  exact
                    joinMemEnvsStrong_lookup_some_of_right_lookup
                      (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt2 := qt_src')
                      hlookup_src'
                rcases hlookup_acc1_exists with ⟨qt_acc1, hlookup_acc1⟩
                have htag_acc1 : qtypGuardTag qt_acc1 = some k :=
                  h_fold_guardTag
                    xs acc1 acc' qt_acc1
                    hfold_tail hlookup_acc1 hlookup_out htag_out
                exact
                  joinMemEnvsStrong_lookup_guardTag_right
                    (env1 := acc.2.1) (env2 := x.memEnv') (l := l)
                    (qt := qt_acc1) (qt2 := qt_src') (k := k)
                    hlookup_acc1 hlookup_src' htag_acc1
              · exact
                  ih (acc := acc1) (acc' := acc') (src' := src') (qt_src' := qt_src')
                    hfold_tail hsrc_tail hlookup_out hlookup_src'
    cases hqt : first.qualType with
    | mk etyp poison pred =>
        simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
          MonadExceptOf.throw, TypecheckM] at _h_join
        cases hcheck :
            (List.foldlM
              (fun x result =>
                match result.qualType with
                | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                  if beqETypSignature etyp resEtyp = false then
                    Except.error
                      (toString "Closure alternatives produced incompatible result types: " ++
                        toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
                  else Except.ok ())
              () rest : Except String Unit) with
        | error err =>
            erw [hcheck] at _h_join
            simp at _h_join
        | ok _ =>
            erw [hcheck] at _h_join
            simp at _h_join
            cases hfold :
                List.foldlM joinStep
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                    first.nextTag') rest with
            | error err =>
                erw [hfold] at _h_join
                simp at _h_join
            | ok a =>
                erw [hfold] at _h_join
                simp at _h_join
                subst res
                have hlookup_res' : a.2.1.lookup l = some qt := by
                  simpa [ctxAfter] using hlookup_res
                have hlookup_src' : src.memEnv'.lookup l = some qt_src := by
                  simpa [ctxAfter] using hlookup_src
                exact
                  h_fold_member_guardTag
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a src qt_src
                    hfold hsrc_rest hlookup_res' htag_res hlookup_src'


lemma joinTypeResults_lookup_member_etyp_compat
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (l : Loc) (qt qt_src : QTyp)
  (hlookup_res : (ctxAfter ctx res).memEnv.lookup l = some qt)
  (hlookup_src : (ctxAfter ctx src).memEnv.lookup l = some qt_src) :
  qt.etyp = qt_src.etyp := by
  have hres_int : qt.etyp = ETyp.int :=
    memEnv_lookup_etyp_int (env := (ctxAfter ctx res).memEnv) l qt hlookup_res
  have hsrc_int : qt_src.etyp = ETyp.int :=
    memEnv_lookup_etyp_int (env := (ctxAfter ctx src).memEnv) l qt_src hlookup_src
  calc
    qt.etyp = ETyp.int := hres_int
    _ = qt_src.etyp := hsrc_int.symm


lemma joinTypeResults_lookup_member_poison_imp
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (l : Loc) (qt qt_src : QTyp)
  (hlookup_res : (ctxAfter ctx res).memEnv.lookup l = some qt)
  (hlookup_src : (ctxAfter ctx src).memEnv.lookup l = some qt_src) :
  qt.poison = false → qt_src.poison = false := by
  intro hclean_out
  rcases (List.mem_cons.mp _hmem_src) with hsrc | hsrc_rest
  · subst src
    exact
      joinTypeResults_lookup_head_poison_imp
        (ctx := ctx) (first := first) (rest := rest) (res := res)
        _h_join l qt qt_src hlookup_res hlookup_src hclean_out
  · let joinStep :
        (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
          TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
      fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
        match result.qualType with
        | ⟨resEtyp, resPoison, resPred⟩ =>
            Except.ok
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 result.memEnv',
                joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred,
                joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 result.regime',
                max acc.2.2.2.2.2.2.1 result.nextLoc',
                max acc.2.2.2.2.2.2.2 result.nextTag')
    have h_fold_poison :
        ∀ (rs' : List TypeResult)
          (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
          (qt_acc : QTyp),
          List.foldlM joinStep acc rs' = .ok acc' →
          acc.2.1.lookup l = some qt_acc →
          acc'.2.1.lookup l = some qt →
          qt.poison = false →
          qt_acc.poison = false := by
      intro rs' acc acc' qt_acc hfold hlookup_acc hlookup_out hclean_out'
      induction rs' generalizing acc acc' qt_acc with
      | nil =>
          simp [List.foldlM_nil, pure, Except.pure] at hfold
          subst acc'
          have hqeq : qt_acc = qt := by
            have hqeq_opt : some qt_acc = some qt := by
              calc
                some qt_acc = acc.2.1.lookup l := hlookup_acc.symm
                _ = some qt := hlookup_out
            exact Option.some.inj hqeq_opt
          subst hqeq
          exact hclean_out'
      | cons x xs ih =>
          cases hqx : x.qualType with
          | mk resEtyp resPoison resPred =>
              simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
              let acc1 :
                  ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
                (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                  joinMemEnvsStrong acc.2.1 x.memEnv',
                  joinPoison acc.2.2.1 resPoison,
                  joinPredicates acc.2.2.2.1 resPred,
                  joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                  joinRegimes acc.2.2.2.2.2.1 x.regime',
                  max acc.2.2.2.2.2.2.1 x.nextLoc',
                  max acc.2.2.2.2.2.2.2 x.nextTag')
              have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
                simpa [acc1] using hfold
              obtain ⟨qt_mid, hlookup_mid⟩ :=
                joinMemEnvsStrong_lookup_some_of_left_lookup
                  (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt1 := qt_acc) hlookup_acc
              have hclean_mid : qt_mid.poison = false :=
                ih (acc := acc1) (acc' := acc') (qt_acc := qt_mid) hfold_tail hlookup_mid hlookup_out
              have hacc_not_none : acc.2.1.lookup l ≠ none := by
                intro hnone
                rw [hlookup_acc] at hnone
                cases hnone
              have hleft_clean :=
                joinMemEnvsStrong_lookup_clean_left
                  (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt := qt_mid)
                  hlookup_mid hclean_mid hacc_not_none
              rcases hleft_clean with ⟨qt_acc', hlookup_acc', _hetyp, hpoison_acc'⟩
              have hqeq : qt_acc' = qt_acc := by
                have hqeq_opt : some qt_acc' = some qt_acc := by
                  calc
                    some qt_acc' = acc.2.1.lookup l := hlookup_acc'.symm
                    _ = some qt_acc := hlookup_acc
                exact Option.some.inj hqeq_opt
              subst hqeq
              exact hpoison_acc'
    have h_fold_member_poison :
        ∀ (rs' : List TypeResult)
          (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
          (src' : TypeResult) (qt_src' : QTyp),
          List.foldlM joinStep acc rs' = .ok acc' →
          src' ∈ rs' →
          acc'.2.1.lookup l = some qt →
          qt.poison = false →
          src'.memEnv'.lookup l = some qt_src' →
          qt_src'.poison = false := by
      intro rs' acc acc' src' qt_src' hfold hmem_src' hlookup_out hclean_out' hlookup_src'
      induction rs' generalizing acc acc' src' qt_src' with
      | nil =>
          cases hmem_src'
      | cons x xs ih =>
          cases hqx : x.qualType with
          | mk resEtyp resPoison resPred =>
              simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
              let acc1 :
                  ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
                (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                  joinMemEnvsStrong acc.2.1 x.memEnv',
                  joinPoison acc.2.2.1 resPoison,
                  joinPredicates acc.2.2.2.1 resPred,
                  joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                  joinRegimes acc.2.2.2.2.2.1 x.regime',
                  max acc.2.2.2.2.2.2.1 x.nextLoc',
                  max acc.2.2.2.2.2.2.2 x.nextTag')
              have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
                simpa [acc1] using hfold
              rcases (List.mem_cons.mp hmem_src') with hsrc_eq | hsrc_tail
              · subst src'
                have hlookup_acc1_exists :
                    ∃ qt_acc1, acc1.2.1.lookup l = some qt_acc1 := by
                  exact
                    joinMemEnvsStrong_lookup_some_of_right_lookup
                      (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt2 := qt_src')
                      hlookup_src'
                rcases hlookup_acc1_exists with ⟨qt_acc1, hlookup_acc1⟩
                have hclean_acc1 : qt_acc1.poison = false :=
                  h_fold_poison
                    xs acc1 acc' qt_acc1
                    hfold_tail hlookup_acc1 hlookup_out hclean_out'
                have hx_not_none : x.memEnv'.lookup l ≠ none := by
                  intro hnone
                  rw [hlookup_src'] at hnone
                  cases hnone
                have hright_clean :=
                  joinMemEnvsStrong_lookup_clean_right
                    (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt := qt_acc1)
                    hlookup_acc1 hclean_acc1 hx_not_none
                rcases hright_clean with ⟨qt_x, hlookup_x, _hetyp_x, hclean_x⟩
                have hqeq : qt_x = qt_src' := by
                  have hqeq_opt : some qt_x = some qt_src' := by
                    calc
                      some qt_x = x.memEnv'.lookup l := hlookup_x.symm
                      _ = some qt_src' := hlookup_src'
                  exact Option.some.inj hqeq_opt
                subst hqeq
                exact hclean_x
              · exact
                  ih (acc := acc1) (acc' := acc') (src' := src') (qt_src' := qt_src')
                    hfold_tail hsrc_tail hlookup_out hlookup_src'
    cases hqt : first.qualType with
    | mk etyp poison pred =>
        simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
          MonadExceptOf.throw, TypecheckM] at _h_join
        cases hcheck :
            (List.foldlM
              (fun x result =>
                match result.qualType with
                | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                  if beqETypSignature etyp resEtyp = false then
                    Except.error
                      (toString "Closure alternatives produced incompatible result types: " ++
                        toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
                  else Except.ok ())
              () rest : Except String Unit) with
        | error err =>
            erw [hcheck] at _h_join
            simp at _h_join
        | ok _ =>
            erw [hcheck] at _h_join
            simp at _h_join
            cases hfold :
                List.foldlM joinStep
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                    first.nextTag') rest with
            | error err =>
                erw [hfold] at _h_join
                simp at _h_join
            | ok a =>
                erw [hfold] at _h_join
                simp at _h_join
                subst res
                have hlookup_res' : a.2.1.lookup l = some qt := by
                  simpa [ctxAfter] using hlookup_res
                have hlookup_src' : src.memEnv'.lookup l = some qt_src := by
                  simpa [ctxAfter] using hlookup_src
                exact
                  h_fold_member_poison
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a src qt_src
                    hfold hsrc_rest hlookup_res' hclean_out hlookup_src'


lemma joinTypeResults_lookup_member_clean_compat
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (l : Loc) (qt qt_src : QTyp)
  (hlookup_res : (ctxAfter ctx res).memEnv.lookup l = some qt)
  (hclean_res : qtypCleanUnder (ctxAfter ctx res).regime qt)
  (hlookup_src : (ctxAfter ctx src).memEnv.lookup l = some qt_src) :
  qtypCleanUnder (ctxAfter ctx src).regime qt_src := by
  cases hclean_res with
  | clean hpoison =>
      exact qtypCleanUnder.clean
        (joinTypeResults_lookup_member_poison_imp
          (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
          _h_join _hmem_src l qt qt_src hlookup_res hlookup_src hpoison)
  | guard k htag hreg hnotfun =>
      have htag_src : qtypGuardTag qt_src = some k :=
        joinTypeResults_lookup_member_guardTag_compat
          (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
          _h_join _hmem_src l qt qt_src k hlookup_res hlookup_src htag
      have hreg_src : (ctxAfter ctx src).regime.lookup? k = some true :=
        joinTypeResults_lookup_member_regime_compat
          (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
          _h_join _hmem_src k true hreg
      have hetyp_eq : qt.etyp = qt_src.etyp :=
        joinTypeResults_lookup_member_etyp_compat
          (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
          _h_join _hmem_src l qt qt_src hlookup_res hlookup_src
      have hnotfun_src : qt_src.etyp.isFunctionType = false := by
        simpa [hetyp_eq.symm] using hnotfun
      exact qtypCleanUnder.guard k htag_src hreg_src hnotfun_src


lemma applyPFnTClosure_mem_subset
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuel : Nat) (tcl : PFnTClosure) (r : TypeResult)
  (happly :
    applyPFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel = .ok r) :
  ∀ l, r.memEnv'.contains l → result2.memEnv'.contains l := by
  intro l hcontains
  cases fuel with
  | zero =>
      simp [applyPFnTClosure] at happly
  | succ fuelBody =>
      cases tcl with
      | regular x body env =>
          rcases applyPFnTClosure_regular_inv
              ctx st1 st2 p p1 argEtyp argPoison argPred result2 fuelBody x body env r happly with
            ⟨result3, htcBody, _hsub, hr⟩
          subst hr
          let bodyCtx : TypeContext :=
            { ctx with
              pc := joinPoison p (joinPoison ctx.pc p1)
              memEnv := result2.memEnv'
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
              tagEnv := result2.tagEnv'
              nextTag := result2.nextTag'
              nextLoc := result2.nextLoc'
              regime := result2.regime' }
          have hsub_body :
              ∀ l, result3.memEnv'.contains l → bodyCtx.memEnv.contains l :=
            typecheckExpr_pure_mem_subset_of_toPExpr
              (ctx := bodyCtx) (e := PExpr.toExpr body) (pe := body)
              (fuel := fuelBody) (res := result3)
              (hpe := by simpa using toExpr_toPExpr? body)
              (htc := by simpa [bodyCtx] using htcBody)
          simpa [bodyCtx] using hsub_body l hcontains
      | extern x retSpec capturedEnv =>
          exact False.elim <|
            applyPFnTClosure_ioFree_extern_fails
              ctx st1 st2 p p1 argEtyp argPoison argPred result2
              (Nat.succ fuelBody) x retSpec capturedEnv r happly

lemma applyPFnTClosure_preserves_memEnv_lookup
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuel : Nat) (tcl : PFnTClosure) (r : TypeResult)
  (happly :
    applyPFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel = .ok r) :
  ∀ l qt, result2.memEnv'.lookup l = some qt → r.memEnv'.lookup l = some qt := by
  intro l qt hlookup
  cases fuel with
  | zero =>
      simp [applyPFnTClosure] at happly
  | succ fuelBody =>
      cases tcl with
      | regular x body env =>
          rcases applyPFnTClosure_regular_inv
              ctx st1 st2 p p1 argEtyp argPoison argPred result2 fuelBody x body env r happly with
            ⟨result3, htcBody, _hsub, hr⟩
          subst hr
          let bodyCtx : TypeContext :=
            { ctx with
              pc := joinPoison p (joinPoison ctx.pc p1)
              memEnv := result2.memEnv'
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
              tagEnv := result2.tagEnv'
              nextTag := result2.nextTag'
              nextLoc := result2.nextLoc'
              regime := result2.regime' }
          have hpres_body :
              ∀ l qt, bodyCtx.memEnv.lookup l = some qt → result3.memEnv'.lookup l = some qt :=
            typecheckExpr_pure_mem_lookup_bridge_of_toPExpr
              (ctx := bodyCtx) (e := PExpr.toExpr body) (pe := body)
              (fuel := fuelBody) (res := result3)
              (hpe := by simpa using toExpr_toPExpr? body)
              (htc := by simpa [bodyCtx] using htcBody)
          simpa [bodyCtx] using hpres_body l qt hlookup
      | extern x retSpec capturedEnv =>
          exact False.elim <|
            applyPFnTClosure_ioFree_extern_fails
              ctx st1 st2 p p1 argEtyp argPoison argPred result2
              (Nat.succ fuelBody) x retSpec capturedEnv r happly

lemma clean_lookup_origin_of_same_qt
  {R R' : Regime} {Γ Γ' : MemoryTypeEnv} {l : Loc} {qt : QTyp}
  (hlookup_in : Γ.lookup l = some qt)
  (_hlookup_out : Γ'.lookup l = some qt)
  (hmono : Regime.monotoneStep R R') :
  qtypCleanUnder R' qt →
  ∃ qt_in, Γ.lookup l = some qt_in ∧ qtypCleanUnder R qt_in := by
  intro hclean
  exact ⟨qt, hlookup_in, cleanUnder_of_monotone hmono hclean⟩

lemma joinMemEnvsStrong_lookup_cleanUnder_left_or_right
  (env1 env2 : MemoryTypeEnv) (R1 R2 : Regime) (l : Loc) (qt : QTyp)
  (hlookup_join : (joinMemEnvsStrong env1 env2).lookup l = some qt)
  (hclean_join : qtypCleanUnder (joinRegimes R1 R2) qt) :
  (∃ qt1, env1.lookup l = some qt1 ∧ qtypCleanUnder R1 qt1) ∨
  (∃ qt2, env2.lookup l = some qt2 ∧ qtypCleanUnder R2 qt2) := by
  have hcontains_join : (joinMemEnvsStrong env1 env2).contains l :=
    memEnv_contains_of_lookup_some (joinMemEnvsStrong env1 env2) l qt hlookup_join
  rcases joinMemEnvsStrong_contains_implies_or env1 env2 l hcontains_join with hcontains1 | hcontains2
  · rcases memEnv_lookup_some_of_contains env1 l hcontains1 with ⟨qt1, hlookup1⟩
    left
    cases hclean_join with
    | clean hpoison =>
        have henv1 : env1.lookup l ≠ none := by
          intro hnone
          rw [hlookup1] at hnone
          contradiction
        rcases joinMemEnvsStrong_lookup_clean_left env1 env2 l qt hlookup_join hpoison henv1 with
          ⟨qt1', hlookup1', _hetyp, hpoison1'⟩
        exact ⟨qt1', hlookup1', qtypCleanUnder.clean hpoison1'⟩
    | guard k htag hk hnotfun =>
        have htag1 : qtypGuardTag qt1 = some k :=
          joinMemEnvsStrong_lookup_guardTag_left env1 env2 l qt qt1 k hlookup_join hlookup1 htag
        have hk1 : R1.lookup? k = some true :=
          joinRegimes_lookup_some_left R1 R2 k true hk
        have hnotfun1 : qt1.etyp.isFunctionType = false := by
          rw [memEnv_lookup_etyp_int env1 l qt1 hlookup1]
          native_decide
        exact ⟨qt1, hlookup1, qtypCleanUnder.guard k htag1 hk1 hnotfun1⟩
  · rcases memEnv_lookup_some_of_contains env2 l hcontains2 with ⟨qt2, hlookup2⟩
    right
    cases hclean_join with
    | clean hpoison =>
        have henv2 : env2.lookup l ≠ none := by
          intro hnone
          rw [hlookup2] at hnone
          contradiction
        rcases joinMemEnvsStrong_lookup_clean_right env1 env2 l qt hlookup_join hpoison henv2 with
          ⟨qt2', hlookup2', _hetyp, hpoison2'⟩
        exact ⟨qt2', hlookup2', qtypCleanUnder.clean hpoison2'⟩
    | guard k htag hk hnotfun =>
        have htag2 : qtypGuardTag qt2 = some k :=
          joinMemEnvsStrong_lookup_guardTag_right env1 env2 l qt qt2 k hlookup_join hlookup2 htag
        have hk2 : R2.lookup? k = some true :=
          joinRegimes_lookup_some_right R1 R2 k true hk
        have hnotfun2 : qt2.etyp.isFunctionType = false := by
          rw [memEnv_lookup_etyp_int env2 l qt2 hlookup2]
          native_decide
        exact ⟨qt2, hlookup2, qtypCleanUnder.guard k htag2 hk2 hnotfun2⟩


lemma typecheckExpr_clean_lookup_origin_of_pc_true
  (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
  (htc : typecheckExpr .ioFree ctx e fuel = .ok res)
  (hpc : ctx.pc = true) :
  ∀ (l : Loc) (qt_out : QTyp),
    res.memEnv'.lookup l = some qt_out →
    qtypCleanUnder res.regime' qt_out →
    ∃ qt_in, ctx.memEnv.lookup l = some qt_in ∧ qtypCleanUnder ctx.regime qt_in := by
  classical
  revert ctx e res htc hpc
  refine Nat.strong_induction_on fuel ?_
  intro fuel ih ctx e res htc hpc l qt_out hlookup_out hclean_out
  cases fuel with
  | zero =>
      simp [typecheckExpr] at htc
  | succ fuel' =>
      have hltSub : fuel' - 1 < Nat.succ fuel' := by
        exact Nat.lt_succ_of_le (Nat.sub_le fuel' 1)
      cases e with
      | num n =>
          simp [typecheckExpr] at htc
          cases htc
          exact ⟨qt_out, hlookup_out, hclean_out⟩
      | bool b =>
          simp [typecheckExpr] at htc
          cases htc
          exact ⟨qt_out, hlookup_out, hclean_out⟩
      | unit =>
          simp [typecheckExpr] at htc
          cases htc
          exact ⟨qt_out, hlookup_out, hclean_out⟩
      | str s =>
          simp [typecheckExpr] at htc
          cases htc
          exact ⟨qt_out, hlookup_out, hclean_out⟩
      | var x =>
          have htcVar : typecheckVar ctx x = .ok res := by
            simpa [typecheckExpr] using htc
          have hmem : res.memEnv' = ctx.memEnv :=
            typecheckVar_preserves_memEnv ctx x res htcVar
          have hreg : res.regime' = ctx.regime :=
            typecheckVar_preserves_regime ctx x res htcVar
          exact ⟨qt_out, by simpa [hmem] using hlookup_out, by simpa [hreg] using hclean_out⟩
      | fn x st1 body st2 =>
          simp [typecheckExpr, typecheckFn] at htc
          cases htc
          exact ⟨qt_out, hlookup_out, hclean_out⟩
      | pfn x st1 body st2 =>
          unfold typecheckExpr at htc
          unfold typecheckPfn at htc
          simp [bind, Except.bind] at htc
          cases h_topexpr : body.toPExpr with
          | error _ =>
              simp [h_topexpr] at htc
          | ok _ =>
              simp [h_topexpr, pure, Except.pure] at htc
              cases htc
              exact ⟨qt_out, hlookup_out, hclean_out⟩
      | op e1 bop e2 =>
          have htcOp : typecheckOp .ioFree ctx e1 e2 fuel' bop = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckOp_structure ctx e1 e2 bop fuel' res htcOp with
            ⟨result1, result2, _result_etyp, htc1, htc2, _h_op, h_mem, _h_tag, _h_loc, _h_ntag,
              h_regime, _h_ret_etyp, _h_ret_poison, _h_ret_pred⟩
          have hlookup2 : result2.memEnv'.lookup l = some qt_out := by
            simpa [h_mem] using hlookup_out
          have hclean2 : qtypCleanUnder result2.regime' qt_out := by
            simpa [h_regime] using hclean_out
          have hpc2 : (updateCtxFromResult ctx result1).pc = true := by
            simpa [updateCtxFromResult] using hpc
          rcases ih (fuel' - 1) hltSub
              (updateCtxFromResult ctx result1) e2 result2
              (by simpa [updateCtxFromResult] using htc2)
              hpc2 l qt_out hlookup2 hclean2 with
            ⟨qt_mid, hlookup_mid, hclean_mid⟩
          rcases ih (fuel' - 1) hltSub ctx e1 result1
              (by simpa using htc1) hpc l qt_mid
              (by simpa [updateCtxFromResult] using hlookup_mid)
              (by simpa [updateCtxFromResult] using hclean_mid) with
            ⟨qt_in, hlookup_in, hclean_in⟩
          exact ⟨qt_in, hlookup_in, hclean_in⟩
      | unaryop uop e1 =>
          have htcUnary : typecheckUnaryOp .ioFree ctx uop e1 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckUnaryOp_structure ctx uop e1 fuel' res htcUnary with
            ⟨result1, _result_etyp, htc1, _h_op, h_mem, _h_tag, _h_loc, _h_ntag, h_regime,
              _h_ret_etyp, _h_ret_poison, _h_ret_pred⟩
          have hlookup1 : result1.memEnv'.lookup l = some qt_out := by
            simpa [h_mem] using hlookup_out
          have hclean1 : qtypCleanUnder result1.regime' qt_out := by
            simpa [h_regime] using hclean_out
          exact ih (fuel' - 1) hltSub ctx e1 result1
            (by simpa using htc1) hpc l qt_out hlookup1 hclean1
      | deref e1 =>
          have htcDeref : typecheckDeref .ioFree ctx e1 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckDeref_structure ctx e1 fuel' res htcDeref with
            ⟨result1, htc1, h_mem, _h_tag, _h_loc, _h_ntag, h_regime⟩
          have hlookup1 : result1.memEnv'.lookup l = some qt_out := by
            simpa [h_mem] using hlookup_out
          have hclean1 : qtypCleanUnder result1.regime' qt_out := by
            simpa [h_regime] using hclean_out
          exact ih (fuel' - 1) hltSub ctx e1 result1
            (by simpa using htc1) hpc l qt_out hlookup1 hclean1
      | seq e1 e2 =>
          have htcSeq : typecheckSeq .ioFree ctx e1 e2 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckSeq_structure ctx e1 e2 fuel' res htcSeq with
            ⟨result1, ctx', htc1, hctx', htc2⟩
          have hpc2 : ctx'.pc = true := by
            simpa [hctx', updateCtxFromResult] using hpc
          rcases ih (fuel' - 1) hltSub ctx' e2 res
              (by simpa [hctx'] using htc2) hpc2 l qt_out hlookup_out hclean_out with
            ⟨qt_mid, hlookup_mid, hclean_mid⟩
          rcases ih (fuel' - 1) hltSub ctx e1 result1
              (by simpa using htc1) hpc l qt_mid
              (by simpa [hctx', updateCtxFromResult] using hlookup_mid)
              (by simpa [hctx', updateCtxFromResult] using hclean_mid) with
            ⟨qt_in, hlookup_in, hclean_in⟩
          exact ⟨qt_in, hlookup_in, hclean_in⟩
      | vlet x e1 e2 =>
          have htcVlet : typecheckVlet .ioFree ctx x e1 e2 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckVlet_structure ctx x e1 e2 fuel' res htcVlet with
            ⟨result1, result2, ctx', htc1, hctx', htc2, _h_ret_etyp, h_mem, _h_tag, _h_loc,
              _h_ntag, h_regime, _h_ret_poison, _h_ret_pred⟩
          have hlookup2 : result2.memEnv'.lookup l = some qt_out := by
            simpa [h_mem] using hlookup_out
          have hclean2 : qtypCleanUnder result2.regime' qt_out := by
            simpa [h_regime] using hclean_out
          have hpc2 : ctx'.pc = true := by
            simpa [hctx'] using hpc
          rcases ih (fuel' - 1) hltSub ctx' e2 result2
              (by simpa [hctx'] using htc2) hpc2 l qt_out hlookup2 hclean2 with
            ⟨qt_mid, hlookup_mid, hclean_mid⟩
          rcases ih (fuel' - 1) hltSub ctx e1 result1
              (by simpa using htc1) hpc l qt_mid
              (by simpa [hctx'] using hlookup_mid)
              (by simpa [hctx'] using hclean_mid) with
            ⟨qt_in, hlookup_in, hclean_in⟩
          exact ⟨qt_in, hlookup_in, hclean_in⟩
      | newRef e1 =>
          have htcNew : typecheckNewRef .ioFree ctx e1 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckNewRef_structure ctx e1 fuel' res htcNew with
            ⟨result1, lfresh, htc1, _hlfresh, _hInt, _hRetEtyp, _hRetPoison, _hRetPred, h_mem,
              _h_tag, _h_nextLoc, _h_nextTag, h_regime⟩
          by_cases hEq : l = lfresh
          · subst l
            have hlookup_stored :
                res.memEnv'.lookup lfresh =
                  some { etyp := ETyp.int
                         poison := true
                         pred := Predicate.noPred } := by
              rw [h_mem]
              simp [hpc, joinPoison, updateMemEnv, MemoryTypeEnv.lookup]
            have hqt : qt_out = { etyp := ETyp.int, poison := true, pred := Predicate.noPred } := by
              have hsomes : some qt_out = some { etyp := ETyp.int, poison := true, pred := Predicate.noPred } := by
                calc
                  some qt_out = res.memEnv'.lookup lfresh := by symm; exact hlookup_out
                  _ = some { etyp := ETyp.int, poison := true, pred := Predicate.noPred } := hlookup_stored
              exact Option.some.inj hsomes
            subst hqt
            exact False.elim ((not_qtypCleanUnder_of_poison_true_noPred rfl rfl) hclean_out)
          · have hlookup1 : result1.memEnv'.lookup l = some qt_out := by
              rw [h_mem] at hlookup_out
              rw [MemoryTypeEnv_lookup_updateMemEnv_ne (l := lfresh) (l' := l)
                    (qt := { etyp := ETyp.int
                             poison := joinPoison ctx.pc result1.qualType.poison
                             pred := if ctx.pc then Predicate.noPred else result1.qualType.pred }) hEq] at hlookup_out
              exact hlookup_out
            have hclean1 : qtypCleanUnder result1.regime' qt_out := by
              simpa [h_regime] using hclean_out
            exact ih (fuel' - 1) hltSub ctx e1 result1
              (by simpa using htc1) hpc l qt_out hlookup1 hclean1
      | assign e1 e2 =>
          have htcAssign : typecheckAssign .ioFree ctx e1 e2 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckAssign_memEnv_formula ctx e1 e2 fuel' res htcAssign with
            ⟨result1, result2, ls, htc1, _hRef, htc2, _hInt, h_mem, h_regime⟩
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
                        (if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred)).lookup l = some qt_out := by
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
                            pred := if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred }).lookup x = some qt_out := by
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
                          (if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred)).lookup l = some qt_out := by
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
                        (ls.toList.foldl (fun acc l0 => updateMemEnv acc l0 finalQt) result2.memEnv').lookup l = some finalQt :=
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
          · have hlookup2 : result2.memEnv'.lookup l = some qt_out := by
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
                _ = some qt_out := hlookup_formula
            have hclean2 : qtypCleanUnder result2.regime' qt_out := by
              have hclean_inv : qtypCleanUnder (invalidateRegimeDeps result2.regime' result2.tagEnv' ls) qt_out := by
                simpa [h_regime] using hclean_out
              exact cleanUnder_of_monotone
                (invalidateRegimeDeps_monotone result2.regime' result2.tagEnv' ls)
                hclean_inv
            have hpc2 : (updateCtxFromResult ctx result1).pc = true := by
              simpa [updateCtxFromResult] using hpc
            rcases ih (fuel' - 1) hltSub
                (updateCtxFromResult ctx result1) e2 result2
                (by simpa [updateCtxFromResult] using htc2)
                hpc2 l qt_out hlookup2 hclean2 with
              ⟨qt_mid, hlookup_mid, hclean_mid⟩
            rcases ih (fuel' - 1) hltSub ctx e1 result1
                (by simpa using htc1) hpc l qt_mid
                (by simpa [updateCtxFromResult] using hlookup_mid)
                (by simpa [updateCtxFromResult] using hclean_mid) with
              ⟨qt_in, hlookup_in, hclean_in⟩
            exact ⟨qt_in, hlookup_in, hclean_in⟩
      | ite e1 e2 e3 =>
          have htcIf : typecheckIf .ioFree ctx e1 e2 e3 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckIf_structure ctx e1 e2 e3 fuel' res htcIf with h1 | h2 | h3 | h4
          · rcases h1 with ⟨k, deps, _hmg, _hk, _res1, _htc1, _hBool, res2, htc2, h_mem, _h_tag,
              _h_nextLoc, _h_nextTag, h_regime, _h_poison, _h_etyp⟩
            let ctxTrue : TypeContext := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ }
            have hpcTrue : ctxTrue.pc = true := by
              simpa [ctxTrue] using hpc
            rcases ih (fuel' - 1) hltSub ctxTrue e2 res2
                (by simpa [ctxTrue] using htc2) hpcTrue l qt_out
                (by simpa [h_mem] using hlookup_out)
                (by simpa [h_regime] using hclean_out) with
              ⟨qt_in, hlookup_in, hclean_in⟩
            exact ⟨qt_in, by simpa [ctxTrue] using hlookup_in, by simpa [ctxTrue] using hclean_in⟩
          · rcases h2 with ⟨k, deps, _hmg, _hk, _res1, _htc1, _hBool, res3, htc3, h_mem, _h_tag,
              _h_nextLoc, _h_nextTag, h_regime, _h_poison, _h_etyp⟩
            let ctxFalse : TypeContext := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩ }
            have hpcFalse : ctxFalse.pc = true := by
              simpa [ctxFalse] using hpc
            rcases ih (fuel' - 1) hltSub ctxFalse e3 res3
                (by simpa [ctxFalse] using htc3) hpcFalse l qt_out
                (by simpa [h_mem] using hlookup_out)
                (by simpa [h_regime] using hclean_out) with
              ⟨qt_in, hlookup_in, hclean_in⟩
            exact ⟨qt_in, by simpa [ctxFalse] using hlookup_in, by simpa [ctxFalse] using hclean_in⟩
          · rcases h3 with ⟨k, deps, _hmg, _hkNone, res1, _htc1, _hBool, res2, htc2, res3, htc3, h_mem,
              _h_tag, _h_nextLoc, _h_nextTag, h_regime, _h_poison, _h_etyp, _h_pred⟩
            have hlookup_join :
                (joinMemEnvsStrong res2.memEnv' res3.memEnv').lookup l = some qt_out := by
              simpa [h_mem] using hlookup_out
            have hclean_join : qtypCleanUnder (joinRegimes res2.regime' res3.regime') qt_out := by
              simpa [h_regime] using hclean_out
            have hbranch :=
              joinMemEnvsStrong_lookup_cleanUnder_left_or_right
                res2.memEnv' res3.memEnv' res2.regime' res3.regime' l qt_out
                hlookup_join hclean_join
            let branchPc := joinPoison ctx.pc res1.qualType.poison
            let ctxTrue : TypeContext := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩, pc := branchPc }
            let ctxFalse : TypeContext := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩, pc := branchPc }
            let ctxFalse' : TypeContext := { ctxFalse with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
            have hpcBranch : branchPc = true := by
              simp [branchPc, hpc, joinPoison]
            have hpcTrue : ctxTrue.pc = true := by
              simp [ctxTrue, hpcBranch]
            have hpcFalse : ctxFalse'.pc = true := by
              simp [ctxFalse', ctxFalse, hpcBranch]
            rcases hbranch with hleft | hright
            · rcases hleft with ⟨qt2, hlookup2, hclean2⟩
              rcases ih (fuel' - 1) hltSub ctxTrue e2 res2
                  (by simpa [ctxTrue, branchPc] using htc2) hpcTrue l qt2 hlookup2 hclean2 with
                ⟨qt_in, hlookup_in, hclean_in⟩
              exact ⟨qt_in, by simpa [ctxTrue] using hlookup_in, by simpa [ctxTrue] using hclean_in⟩
            · rcases hright with ⟨qt3, hlookup3, hclean3⟩
              rcases ih (fuel' - 1) hltSub ctxFalse' e3 res3
                  (by simpa [ctxFalse', ctxFalse, branchPc] using htc3) hpcFalse l qt3 hlookup3 hclean3 with
                ⟨qt_in, hlookup_in, hclean_in⟩
              exact ⟨qt_in, by simpa [ctxFalse', ctxFalse] using hlookup_in, by simpa [ctxFalse', ctxFalse] using hclean_in⟩
          · rcases h4 with ⟨_herr, res1, htc1, _hBool, res2, htc2, res3, htc3, h_mem, _h_tag,
              _h_nextLoc, _h_nextTag, h_regime, _h_poison, _h_etyp, _h_pred⟩
            have hlookup_join :
                (joinMemEnvsStrong res2.memEnv' res3.memEnv').lookup l = some qt_out := by
              simpa [h_mem] using hlookup_out
            have hclean_join : qtypCleanUnder (joinRegimes res2.regime' res3.regime') qt_out := by
              simpa [h_regime] using hclean_out
            have hbranch :=
              joinMemEnvsStrong_lookup_cleanUnder_left_or_right
                res2.memEnv' res3.memEnv' res2.regime' res3.regime' l qt_out
                hlookup_join hclean_join
            let ctx' : TypeContext := ctxAfter ctx res1
            let pc' := joinPoison ctx.pc res1.qualType.poison
            let ctx'' : TypeContext := { ctx' with pc := pc' }
            let ctxForE3 : TypeContext := { ctx'' with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
            have hpc'' : ctx''.pc = true := by
              simp [ctx'', pc', hpc, joinPoison]
            rcases hbranch with hleft | hright
            · rcases hleft with ⟨qt2, hlookup2, hclean2⟩
              rcases ih (fuel' - 1) hltSub ctx'' e2 res2
                  (by simpa [ctx'', ctx', pc', ctxAfter] using htc2) hpc'' l qt2 hlookup2 hclean2 with
                ⟨qt_mid, hlookup_mid, hclean_mid⟩
              rcases ih (fuel' - 1) hltSub ctx e1 res1
                  (by simpa using htc1) hpc l qt_mid
                  (by simpa [ctx'', ctx', ctxAfter] using hlookup_mid)
                  (by simpa [ctx'', ctx', ctxAfter] using hclean_mid) with
                ⟨qt_in, hlookup_in, hclean_in⟩
              exact ⟨qt_in, hlookup_in, hclean_in⟩
            · rcases hright with ⟨qt3, hlookup3, hclean3⟩
              rcases ih (fuel' - 1) hltSub ctxForE3 e3 res3
                  (by simpa [ctxForE3, ctx'', ctx', pc', ctxAfter] using htc3)
                  (by simp [ctxForE3, ctx'', pc', hpc, joinPoison]) l qt3 hlookup3 hclean3 with
                ⟨qt_mid, hlookup_mid, hclean_mid⟩
              rcases ih (fuel' - 1) hltSub ctx e1 res1
                  (by simpa using htc1) hpc l qt_mid
                  (by simpa [ctxForE3, ctx'', ctx', ctxAfter] using hlookup_mid)
                  (by simpa [ctxForE3, ctx'', ctx', ctxAfter] using hclean_mid) with
                ⟨qt_in, hlookup_in, hclean_in⟩
              exact ⟨qt_in, hlookup_in, hclean_in⟩
      | app e1 e2 =>
          have htcApp : typecheckApp .ioFree ctx e1 e2 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          cases fuel' with
          | zero =>
              simp [typecheckApp] at htcApp
          | succ fuelApp =>
              obtain ⟨result2, result1, etyp2, p2, pred2, _hqt2, htc2, htc1, hcases⟩ :=
                typecheckApp_arrow_structure_full ctx e1 e2 fuelApp res htcApp
              let ctxFun : TypeContext :=
                { ctx with
                  memEnv := result2.memEnv'
                  tagEnv := result2.tagEnv'
                  nextLoc := result2.nextLoc'
                  nextTag := result2.nextTag'
                  regime := result2.regime' }
              have hpcFun : ctxFun.pc = true := by
                simpa [ctxFun] using hpc
              have hbackToCtx :
                  ∀ qt_mid,
                    result1.memEnv'.lookup l = some qt_mid →
                    qtypCleanUnder result1.regime' qt_mid →
                    ∃ qt_in, ctx.memEnv.lookup l = some qt_in ∧ qtypCleanUnder ctx.regime qt_in := by
                intro qt_mid hlookup_mid hclean_mid
                rcases ih fuelApp (by omega) ctxFun e1 result1
                    (by simpa [ctxFun] using htc1) hpcFun l qt_mid hlookup_mid hclean_mid with
                  ⟨qt_arg, hlookup_arg, hclean_arg⟩
                rcases ih fuelApp (by omega) ctx e2 result2
                    (by simpa using htc2) hpc l qt_arg
                    (by simpa [ctxFun] using hlookup_arg)
                    (by simpa [ctxFun] using hclean_arg) with
                  ⟨qt_in, hlookup_in, hclean_in⟩
                exact ⟨qt_in, hlookup_in, hclean_in⟩
              have hcontains_res : res.memEnv'.contains l := by
                exact memEnv_contains_of_lookup_some res.memEnv' l qt_out hlookup_out
              have hlookup_res_ctx :
                  (ctxAfter ctx res).memEnv.lookup l = some qt_out := by
                simpa [ctxAfter] using hlookup_out
              have hclean_res_ctx :
                  qtypCleanUnder (ctxAfter ctx res).regime qt_out := by
                simpa [ctxAfter] using hclean_out
              cases hcases with
              | inl harrow =>
                  obtain ⟨st1, st2, p, p1, tcls, results, first, rest, _hetyp1, _hp1,
                      _hnpure, _hnempty, _hsub, hmap, heq_results, h_join⟩ := harrow
                  have hmember_origin :
                      ∀ srcRes, srcRes ∈ first :: rest → srcRes.memEnv'.contains l →
                        ∃ qt_in, ctx.memEnv.lookup l = some qt_in ∧ qtypCleanUnder ctx.regime qt_in := by
                    intro srcRes hsrc_mem hsrc_contains
                    have hsrc_results : srcRes ∈ results := by
                      simpa [heq_results] using hsrc_mem
                    rcases list_mapM_ok_mem_output_exists_input
                        (f := fun tcl =>
                          applyFnTClosure .ioFree tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuelApp)
                        (xs := tcls) (ys := results) (y := srcRes)
                        hmap hsrc_results with
                      ⟨tcl, _htcl_mem, happly_src⟩
                    rcases memEnv_lookup_some_of_contains srcRes.memEnv' l hsrc_contains with
                      ⟨qt_src, hlookup_src⟩
                    have hlookup_src_ctx :
                        (ctxAfter ctx srcRes).memEnv.lookup l = some qt_src := by
                      simpa [ctxAfter] using hlookup_src
                    have hclean_src_ctx :
                        qtypCleanUnder (ctxAfter ctx srcRes).regime qt_src := by
                      exact
                        joinTypeResults_lookup_member_clean_compat
                          (ctx := ctx) (first := first) (src := srcRes) (rest := rest) (res := res)
                          h_join hsrc_mem l qt_out qt_src hlookup_res_ctx hclean_res_ctx hlookup_src_ctx
                    cases tcl with
                    | regular x body tenv =>
                        rcases applyFnTClosure_regular_structure
                            ctx st1 st2 p p1 etyp2 p2 pred2 result1 fuelApp x body tenv
                            srcRes happly_src with
                          ⟨fuelBody, hfuelBody⟩
                        have happly_succ :
                            applyFnTClosure .ioFree (FnTClosure.regular x body tenv)
                              st1 st2 p p1 etyp2 p2 pred2 ctx result1 (Nat.succ fuelBody) = .ok srcRes := by
                          simpa [hfuelBody] using happly_src
                        rcases applyFnTClosure_regular_inv
                            ctx st1 st2 p p1 etyp2 p2 pred2 result1 fuelBody x body tenv srcRes
                            happly_succ with
                          ⟨result3, htcBody, _hsubBody, hr⟩
                        let bodyCtx : TypeContext :=
                          { ctx with
                            pc := joinPoison p (joinPoison p1 ctx.pc)
                            memEnv := result1.memEnv'
                            varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
                              ⟨etyp2, joinPoison ctx.pc p2, pred2⟩
                            tagEnv := result1.tagEnv'
                            nextTag := result1.nextTag'
                            nextLoc := result1.nextLoc'
                            regime := result1.regime' }
                        have hpcBody : bodyCtx.pc = true := by
                          simp [bodyCtx, hpc, joinPoison]
                        have hlookup_result3 : result3.memEnv'.lookup l = some qt_src := by
                          simpa [hr] using hlookup_src
                        have hclean_result3 : qtypCleanUnder result3.regime' qt_src := by
                          simpa [ctxAfter, hr] using hclean_src_ctx
                        rcases ih fuelBody (by omega) bodyCtx body result3
                            (by simpa [bodyCtx] using htcBody)
                            hpcBody l qt_src hlookup_result3 hclean_result3 with
                          ⟨qt_mid, hlookup_mid_body, hclean_mid_body⟩
                        exact
                          hbackToCtx qt_mid
                            (by simpa [bodyCtx] using hlookup_mid_body)
                            (by simpa [bodyCtx] using hclean_mid_body)
                    | extern x retSpec effects capturedEnv =>
                        exact False.elim <|
                          applyFnTClosure_ioFree_extern_fails
                            ctx st1 st2 p p1 etyp2 p2 pred2 result1 fuelApp
                            x retSpec effects capturedEnv srcRes happly_src
                  rcases joinTypeResults_mem_contains_head_or_rest
                      ctx first rest res h_join l hcontains_res with
                    hhead | ⟨srcRes, hsrc_rest, hsrc_contains⟩
                  · exact hmember_origin first (by simp) hhead
                  · exact hmember_origin srcRes (List.mem_cons_of_mem _ hsrc_rest) hsrc_contains
              | inr hparrow =>
                  obtain ⟨st1, st2, p, p1, tcls, results, first, rest, _hetyp1, _hp1,
                      _hnempty, _hsub, hmap, heq_results, h_join⟩ := hparrow
                  have hmember_origin :
                      ∀ srcRes, srcRes ∈ first :: rest → srcRes.memEnv'.contains l →
                        ∃ qt_in, ctx.memEnv.lookup l = some qt_in ∧ qtypCleanUnder ctx.regime qt_in := by
                    intro srcRes hsrc_mem hsrc_contains
                    have hsrc_results : srcRes ∈ results := by
                      simpa [heq_results] using hsrc_mem
                    rcases list_mapM_ok_mem_output_exists_input
                        (f := fun tcl =>
                          applyPFnTClosure .ioFree tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuelApp)
                        (xs := tcls) (ys := results) (y := srcRes)
                        hmap hsrc_results with
                      ⟨tcl, _htcl_mem, happly_src⟩
                    rcases memEnv_lookup_some_of_contains srcRes.memEnv' l hsrc_contains with
                      ⟨qt_src, hlookup_src⟩
                    have hlookup_src_ctx :
                        (ctxAfter ctx srcRes).memEnv.lookup l = some qt_src := by
                      simpa [ctxAfter] using hlookup_src
                    have hclean_src_ctx :
                        qtypCleanUnder (ctxAfter ctx srcRes).regime qt_src := by
                      exact
                        joinTypeResults_lookup_member_clean_compat
                          (ctx := ctx) (first := first) (src := srcRes) (rest := rest) (res := res)
                          h_join hsrc_mem l qt_out qt_src hlookup_res_ctx hclean_res_ctx hlookup_src_ctx
                    cases tcl with
                    | regular x pbody tenv =>
                        have hcontains_result1 : result1.memEnv'.contains l := by
                          exact
                            applyPFnTClosure_mem_subset
                              (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                              (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                              (result2 := result1) (fuel := fuelApp)
                              (tcl := PFnTClosure.regular x pbody tenv) (r := srcRes)
                              happly_src l hsrc_contains
                        rcases memEnv_lookup_some_of_contains result1.memEnv' l hcontains_result1 with
                          ⟨qt_mid, hlookup_mid⟩
                        have hlookup_preserved :
                            srcRes.memEnv'.lookup l = some qt_mid := by
                          exact
                            applyPFnTClosure_preserves_memEnv_lookup
                              (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                              (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                              (result2 := result1) (fuel := fuelApp)
                              (tcl := PFnTClosure.regular x pbody tenv) (r := srcRes)
                              happly_src l qt_mid hlookup_mid
                        have hqt_mid : qt_src = qt_mid := by
                          rw [hlookup_src] at hlookup_preserved
                          exact Option.some.inj hlookup_preserved
                        have hmono_src : Regime.monotoneStep result1.regime' srcRes.regime' := by
                          exact
                            applyPFnTClosure_regime_mono
                              (tcl := PFnTClosure.regular x pbody tenv)
                              (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                              (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                              (r1 := result1) (r2 := srcRes) (fuel := fuelApp)
                              (IH := fun m _hlt e ctx' res' htc' =>
                                by
                                  simpa [typecheck] using regime_monotone ctx' e m res' htc')
                              happly_src
                        have hclean_mid : qtypCleanUnder result1.regime' qt_mid := by
                          simpa [hqt_mid] using
                            (cleanUnder_of_monotone hmono_src
                              (by simpa [ctxAfter] using hclean_src_ctx) :
                                qtypCleanUnder result1.regime' qt_src)
                        exact hbackToCtx qt_mid hlookup_mid hclean_mid
                    | extern x retSpec capturedEnv =>
                        exact False.elim <|
                          applyPFnTClosure_ioFree_extern_fails
                            ctx st1 st2 p p1 etyp2 p2 pred2 result1 fuelApp
                            x retSpec capturedEnv srcRes happly_src
                  rcases joinTypeResults_mem_contains_head_or_rest
                      ctx first rest res h_join l hcontains_res with
                    hhead | ⟨srcRes, hsrc_rest, hsrc_contains⟩
                  · exact hmember_origin first (by simp) hhead
                  · exact hmember_origin srcRes (List.mem_cons_of_mem _ hsrc_rest) hsrc_contains
      | kwhile e1 e2 =>
          -- Permanently postponed: `kwhile` proofs are out of active scope for this work.
          sorry
      | rand e1 =>
          have htcRand : typecheckRand .ioFree ctx e1 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          exact absurd htcRand (typecheckRand_ioFree_impossible ctx e1 fuel' res)
      | frand e1 =>
          have htcFrand : typecheckFrand .ioFree ctx e1 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          exact absurd htcFrand (typecheckFrand_ioFree_impossible ctx e1 fuel' res)
      | printInt e1 =>
          have htcPrint : typecheckPrintInt .ioFree ctx e1 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          exact absurd htcPrint (typecheckPrintInt_ioFree_impossible ctx e1 fuel' res)
      | printString e1 =>
          have htcPrint : typecheckPrintString .ioFree ctx e1 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          exact absurd htcPrint (typecheckPrintString_ioFree_impossible ctx e1 fuel' res)
      | externVal typ poison pred =>
          have heq : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by
            native_decide
          simp [typecheckExpr, typecheckExternVal, heq, bind, Except.bind] at htc
      | externFn arg argTyp retSpec effects =>
          have heq : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by
            native_decide
          simp [typecheckExpr, typecheckExternFn, heq, bind, Except.bind] at htc
      | externPfn arg argTyp retSpec =>
          have heq : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by
            native_decide
          simp [typecheckExpr, typecheckExternPfn, heq, bind, Except.bind] at htc


lemma typecheckExpr_lookup_clean_back_of_pc_true
  (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
  (htc : typecheckExpr .ioFree ctx e fuel = .ok res)
  (hpc : ctx.pc = true) :
  ∀ (l : Loc) (qt_in qt_out : QTyp),
    ctx.memEnv.lookup l = some qt_in →
    res.memEnv'.lookup l = some qt_out →
    qtypCleanUnder res.regime' qt_out →
    qtypCleanUnder ctx.regime qt_in := by
  intro l qt_in qt_out hlookup_in hlookup_out hclean_out
  rcases typecheckExpr_clean_lookup_origin_of_pc_true
      (ctx := ctx) (e := e) (fuel := fuel) (res := res)
      htc hpc l qt_out hlookup_out hclean_out with
    ⟨qt_in', hlookup_in', hclean_in'⟩
  have hqt : qt_in' = qt_in := by
    rw [hlookup_in] at hlookup_in'
    exact Option.some.inj hlookup_in'.symm
  subst hqt
  exact hclean_in'
