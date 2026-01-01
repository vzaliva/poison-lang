-- Formal properties of the poison language: Helper Lemmas for Lookup/Update Operations

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.BigStep
import LeanProofs.Equality
import LeanProofs.IOHelpers
import Mathlib.Data.Nat.Basic  -- for Nat.strong_induction_on
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Std.Data.ExtTreeMap.Lemmas

import Init.Data.List
import Init.Data.List.Lemmas
import Mathlib.Data.List.Lattice
import Batteries.Data.List.Lemmas

open Std

-- ================================================================
-- Helper Lemmas for Lookup/Update Operations
-- ================================================================

-- General lemma: If y ≠ x, then List.lookup y ((x, v) :: l) = List.lookup y l
-- This holds for any association list because update prepends, and lookup skips non-matching keys
lemma List_lookup_cons_ne {α β : Type} [BEq α] [LawfulBEq α] (l : List (α × β)) (x y : α) (v : β) (h_ne : y ≠ x) :
  List.lookup y ((x, v) :: l) = List.lookup y l := by
  simp [List.lookup]
  -- Use by_cases on the boolean equality check
  by_cases h_beq : (y == x) = true
  · -- Case: (y == x) = true, which contradicts h_ne : y ≠ x
    have h_eq : y = x := LawfulBEq.eq_of_beq h_beq
    contradiction
  · -- Case: (y == x) ≠ true, so (y == x) = false
    have h_false : (y == x) = false := by
      cases h : y == x
      · rfl
      · contradiction
    simp [h_false]

-- CapturedVarEnv ↔ list convenience lemmas
@[simp] lemma CapturedVarEnv.lookup_eq (env : CapturedVarEnv) (x : Name) :
  CapturedVarEnv.lookup env x = List.lookup x env := rfl

@[simp] lemma CapturedVarEnv.update_eq (env : CapturedVarEnv) (x : Name) (qt : QTyp) :
  CapturedVarEnv.update env x qt = (x, qt) :: env := rfl

@[simp] lemma CapturedVarEnv.hasKey_iff (env : CapturedVarEnv) (x : Name) :
  CapturedVarEnv.hasKey env x ↔ List.lookup x env ≠ none := by
  rfl

-- If y ≠ x, then updating env with x doesn't affect lookup y
lemma VarTypeEnv_lookup_update_eq (env : VarTypeEnv) (x : Name) (qt : QTyp) :
  (env.update x qt).lookup x = some qt := by
  simp [VarTypeEnv.update, VarTypeEnv.lookup]

-- If y ≠ x, then updating env with x doesn't affect lookup y
lemma VarTypeEnv_lookup_update_ne (env : VarTypeEnv) (x y : Name) (qt : QTyp) (h_ne : y ≠ x) :
  (env.update x qt).lookup y = env.lookup y := by
  by_cases h_eq : varTypeEnvCmp x y = .eq
  · have h_xy : x = y := LawfulEqCmp.eq_of_compare h_eq
    exact (h_ne h_xy.symm).elim
  · simp [VarTypeEnv.update, VarTypeEnv.lookup, ExtTreeMap.getElem?_insert, h_eq]

-- If y ≠ x, then updating env with x doesn't affect lookup y
lemma VarEnv_lookup_update_ne (env : VarEnv) (x y : Name) (v : Value) (h_ne : y ≠ x) :
  (env.update x v).lookup y = env.lookup y := by
  simp [VarEnv.update, VarEnv.lookup]
  exact List_lookup_cons_ne env x y v h_ne

-- ================================================================
-- ExtTreeMap Injectivity Preservation
-- ================================================================

-- Helper lemma: ExtTreeMap.insert preserves injectivity when inserting a fresh value
-- If m is injective and v is fresh (not in range), then m.insert k v is injective
-- Note: Without the "v is fresh" premise, the lemma is false (counterexample: if m[k₂]? = some v
-- and we insert k with value v where k ≠ k₂, then both k and k₂ map to v, violating injectivity)
lemma ExtTreeMap_insert_preserves_injectivity
    {α : Type} {compare : α → α → Ordering} [TransCmp compare] [LawfulEqCmp compare]
    {β : Type} (m : ExtTreeMap α β compare) (k : α) (v : β)
    (h_fresh_value : ∀ k', m.get? k' ≠ some v)
    (h_inj : ∀ k₁ k₂ a, m.get? k₁ = some a → m.get? k₂ = some a → k₁ = k₂) :
  ∀ k₁ k₂ a, (m.insert k v).get? k₁ = some a → (m.insert k v).get? k₂ = some a → k₁ = k₂ := by
  intro k₁ k₂ a hlookup1 hlookup2
  -- Convert to getElem? to use ExtTreeMap.getElem?_insert
  rw [ExtTreeMap.get?_eq_getElem?] at hlookup1 hlookup2
  -- Use ExtTreeMap.getElem?_insert: (t.insert k v)[a]? = if cmp k a = Ordering.eq then some v else t[a]?
  simp only [ExtTreeMap.getElem?_insert] at hlookup1 hlookup2
  -- Case analysis on whether k₁ = k and k₂ = k
  by_cases h_eq1 : compare k k₁ = Ordering.eq
  · -- k₁ = k
    have h_k_eq : k = k₁ := LawfulEqCmp.eq_of_compare h_eq1
    have h_k1_eq : k₁ = k := h_k_eq.symm
    simp [h_eq1] at hlookup1
    -- hlookup1 is now: v = a (simp simplifies some v = some a to v = a)
    subst hlookup1
    -- Now hlookup2: (m.insert k v)[k₂]? = some v
    by_cases h_eq2 : compare k k₂ = Ordering.eq
    · -- k₂ = k, so k₁ = k₂
      have h_k_eq2 : k = k₂ := LawfulEqCmp.eq_of_compare h_eq2
      have h_k2_eq : k₂ = k := h_k_eq2.symm
      simp [h_eq2] at hlookup2
      -- hlookup2 is now: some v = some v, which is true
      -- So we have k₁ = k and k₂ = k, so k₁ = k₂
      rw [h_k1_eq, h_k2_eq]
    · -- k₂ ≠ k, so (m.insert k v)[k₂]? = m[k₂]?
      simp [h_eq2] at hlookup2
      -- We have: m[k₂]? = some v
      -- But h_fresh_value says: ∀ k', m.get? k' ≠ some v
      -- This contradicts hlookup2, so this case is impossible
      have h_contra : m.get? k₂ ≠ some v := h_fresh_value k₂
      contradiction
  · -- k₁ ≠ k, so (m.insert k v)[k₁]? = m[k₁]?
    simp [h_eq1] at hlookup1
    by_cases h_eq2 : compare k k₂ = Ordering.eq
    · -- k₂ = k, similar to above (symmetric case)
      have h_k_eq2 : k = k₂ := LawfulEqCmp.eq_of_compare h_eq2
      have h_k2_eq : k₂ = k := h_k_eq2.symm
      simp [h_eq2] at hlookup2
      -- hlookup2 is now: v = a (simp simplifies some v = some a to v = a)
      subst hlookup2
      -- We have: m[k₁]? = some v
      -- But h_fresh_value says: ∀ k', m.get? k' ≠ some v
      -- This contradicts hlookup1, so this case is impossible
      have h_contra : m.get? k₁ ≠ some v := h_fresh_value k₁
      contradiction
    · -- k₂ ≠ k, so (m.insert k v)[k₂]? = m[k₂]?
      simp [h_eq2] at hlookup2
      -- Both lookups come from m, so use injectivity of m
      -- Convert back to get? for h_inj
      rw [← ExtTreeMap.get?_eq_getElem?] at hlookup1 hlookup2
      exact h_inj k₁ k₂ a hlookup1 hlookup2
